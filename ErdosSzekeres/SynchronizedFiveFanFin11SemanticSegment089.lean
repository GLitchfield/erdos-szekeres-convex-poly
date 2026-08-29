module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment088

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 089. -/

theorem synchronizedFiveFanFin11Semantic_clause06409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1226,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06410 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1226,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06411 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1226,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06412 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1226,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06413 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1228 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0780 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1228 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06414 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0780 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1669 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06415 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0842,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06416 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0842,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06417 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0842,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06418 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0842,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06419 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0781 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0842,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06420 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1229 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0781 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1229 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06421 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1229 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0842 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06422 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0781 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0781 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1670 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06423 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1354,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06424 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1354,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06425 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1354,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06426 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1354,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06427 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1354,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06428 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1230 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0782 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1230 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06429 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0782 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0782 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1671 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06430 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06431 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06432 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06433 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06434 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06435 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1610,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06436 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0783 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06437 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1610 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06438 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause06439 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06440 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06441 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1231 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06442 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0783 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06443 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1610 chi).mpr
  have hright0 : chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06444 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause06445 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06446 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0783 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1672 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0783 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1672 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1610 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06447 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0784 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0784 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0906,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06448 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1232 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0784 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0784 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1232 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06449 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0784 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0784 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1673 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06450 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0785 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0785 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1418,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06451 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1233 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0785 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0785 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1233 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06452 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0785 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0785 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1674 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06453 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1674,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06454 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1674,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06455 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1674,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06456 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1674,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1674,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1234 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0786 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1234 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06459 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1234 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1674 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06460 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0786 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0786 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1675 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06461 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1802,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06462 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1802,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06463 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1802,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06464 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1802,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06465 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1802,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06466 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1235 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0787 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1235 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06467 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0787 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0787 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06468 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1676 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1802 chi).mpr
  have hright0 : chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06469 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0788 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0242,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0788 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0242,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06471 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0788 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0242,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06472 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1236 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0788 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0788 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1236 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06473 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0788 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0788 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1677 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06474 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06475 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06476 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06477 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06478 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0370,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06479 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1237 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0789 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1237 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06480 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0789 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0789 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1678 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
