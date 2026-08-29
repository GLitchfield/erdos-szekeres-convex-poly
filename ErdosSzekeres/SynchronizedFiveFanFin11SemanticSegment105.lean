module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment104

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 105. -/

theorem synchronizedFiveFanFin11Semantic_clause07549 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1392,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07550 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1392,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07551 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1370 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0930 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07552 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1370 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1392 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause07553 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0930 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07554 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1392 chi).mpr
  have hright0 : chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07555 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1810 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1810 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1392 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause07556 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07557 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07558 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07559 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07560 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07561 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1648,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07562 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1371 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0931 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07563 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1371 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1648 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause07564 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0931 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0931 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1811 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07565 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0932 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0932 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0944,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07566 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0932 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0932 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0944,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07567 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1372 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0932 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0932 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1372 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07568 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0933 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0933 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1456,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07569 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0933 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0933 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1456,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07570 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1373 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0933 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0933 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1373 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07571 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0933 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0933 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1812 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07572 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0934 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1712,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07573 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0934 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1712,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07574 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0934 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1712,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07575 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0934 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1712,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07576 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1374 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0934 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1374 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07577 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1813 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0934 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0934 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1813 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07578 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0935 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07579 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0935 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07580 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0935 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07581 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0935 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07582 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0935 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1840,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07583 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0935 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1375 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07584 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1814 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0935 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0935 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1814 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0936 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0936 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0976,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1376 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0936 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0936 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1376 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0467 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07588 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07589 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07590 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07591 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0937 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07592 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1377 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0937 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1377 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07593 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1815 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0937 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0937 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1815 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07594 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0938 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0938 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07596 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0938 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07597 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0938 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07598 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0938 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1378 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0938 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1378 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07600 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0938 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0938 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1816 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07601 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07602 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07603 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07604 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07605 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0939 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07606 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0939 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1379 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07607 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1817 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0939 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0939 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1817 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07608 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0940 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0940 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1936,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07609 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0940 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0940 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1936,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07610 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1380 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0940 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0940 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1380 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07611 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0941 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0941 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0992,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1818 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0941 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0941 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1818 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07613 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0942 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0942 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1504,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07614 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0942 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0942 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1504,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07615 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0942 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0942 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1504,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07616 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0942 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0942 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1504,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0942 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0942 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1819 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07618 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07619 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1760,
  ] at hbad
  tauto

end ErdosSzekeres

end
