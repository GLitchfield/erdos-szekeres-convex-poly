module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment061

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 062. -/

theorem synchronizedFiveFanFin11Semantic_clause04465 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04466 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04467 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04468 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04469 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0993 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0538 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0993 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0993 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0993 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0779 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04471 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0538 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04472 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1431 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0779 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04473 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1291,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04474 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1291,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04475 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1291,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04476 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1291,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04477 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1291,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04478 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0994 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0539 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0994 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04479 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0539 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0539 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1432 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04480 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04481 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04482 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04483 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04484 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04485 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0540 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0995 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04486 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0540 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04487 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1433 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1547 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04488 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1547 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04489 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0540 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0540 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1433 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1547 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04490 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04491 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04492 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04493 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04494 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04495 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0115,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04496 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0541 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0996 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0115 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04498 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0996 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0996 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0115 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04499 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0541 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0541 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04500 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1434 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1434 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0115 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04501 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0179,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04502 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0179,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04503 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0188 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0179,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04504 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0179,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04505 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0179,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04506 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0997 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0542 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0997 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04507 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1435 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0542 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0542 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1435 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04508 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0307,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04509 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0307,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04510 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0307,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04511 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0307,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04512 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0307,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04513 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0998 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0543 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0998 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04514 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1436 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0543 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0543 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1436 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04515 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04516 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04517 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04518 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04519 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04520 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0563,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04521 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0999 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0544 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0999 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04522 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0544 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04523 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1437 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0563 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04524 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0544 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0544 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1437 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0563 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04525 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1075,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04526 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1075,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04527 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1075,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04528 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1075,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04529 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1075,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04530 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0545 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04531 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1000 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1000 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1075 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04532 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0545 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04533 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1075 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04534 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0545 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0545 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1438 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1075 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04535 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0211,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04536 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0211,
  ] at hbad
  tauto

end ErdosSzekeres

end
