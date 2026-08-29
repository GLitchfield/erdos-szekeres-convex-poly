module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment075

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 076. -/

theorem synchronizedFiveFanFin11Semantic_clause05473 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1353,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05474 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0659 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1111 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05475 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1111 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1353 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05476 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1111 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1111 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1353 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11Semantic_clause05477 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0659 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1552 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05478 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1552 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1552 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1353 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05479 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05480 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05481 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05482 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05483 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1609,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05484 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0660 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05485 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1609 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05486 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1112 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1609 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause05487 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1112 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1112 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1609 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05488 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0660 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05489 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1609 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause05490 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1609 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause05491 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0660 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0660 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1553 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1609 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11Semantic_clause05492 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0661 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1417,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05493 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0282 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0282 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0661 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1417,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05494 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0661 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0661 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1113 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05495 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0661 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0661 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1554 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05496 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0246 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0246 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0662 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1673,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0662 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1673,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05498 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0662 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1673,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05499 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0662 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0662 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1114 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05500 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0662 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0662 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1555 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05501 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1801,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05502 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1801,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05503 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1801,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05504 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1801,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05505 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1801,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05506 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0663 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1115 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05507 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1115 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1801 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05508 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0663 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0663 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1556 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05509 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0241,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05510 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0241,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05511 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0241,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05512 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0241,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05513 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0664 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1116 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05514 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0664 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0664 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1557 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05515 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0369,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05516 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0369,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05517 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0369,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05518 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0369,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05519 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0369,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05520 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0665 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1117 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05521 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0665 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0665 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1558 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05522 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0625,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05523 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0625,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05524 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0625,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05525 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0625,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05526 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0625,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05527 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0666 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1118 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05528 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0666 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1559 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05529 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1559 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1559 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0625 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05530 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0666 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1559 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0666 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1559 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0625 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05531 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1137,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05532 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1137,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05533 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1137,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05534 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1137,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05535 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1137,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05536 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0667 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1119 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05537 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1119 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1119 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1137 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05538 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1119 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1119 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1137 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05539 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0667 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0667 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1560 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05540 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0433,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05541 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0433,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05542 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0269 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0269 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0433,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05543 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0433,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05544 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0668 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1120 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
