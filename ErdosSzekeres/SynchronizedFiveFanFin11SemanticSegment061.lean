module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment060

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 061. -/

theorem synchronizedFiveFanFin11Semantic_clause04393 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04394 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04395 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04396 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0984 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0529 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0984 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1422 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0529 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04398 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1422 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0555 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1422 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0555 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause04400 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1067,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04401 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1067,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04402 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1067,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04403 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1067,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04404 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1067,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04405 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0985 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0530 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0985 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04406 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0530 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0530 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04407 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1423 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1423 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1067 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04408 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0203,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0203,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04410 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0203,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04411 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0241 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0203,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04412 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0203,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04413 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0986 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0531 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0986 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04414 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1424 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0531 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0531 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1424 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04415 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04416 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04417 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04418 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04419 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04420 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0331,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04421 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0532 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0987 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04422 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0532 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04423 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0532 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0532 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1425 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0331 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause04424 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0587,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04425 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0587,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04426 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0587,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04427 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0587,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04428 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0587,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04429 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0988 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0533 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04430 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause04431 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause04432 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0988 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0988 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04433 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0533 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04434 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0587 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04435 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11Semantic_clause04436 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04437 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0533 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0533 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1426 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause04438 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1099,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04439 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1099,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04440 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1099,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04441 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1099,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04442 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1099,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04443 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0989 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0534 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0989 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04444 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0534 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0534 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04445 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1427 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1427 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1099 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04446 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0535 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0535 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0395,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04447 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0535 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0328 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0535 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0395,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04448 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0990 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0535 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0535 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0990 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04449 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1428 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0535 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0535 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1428 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04450 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0651,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04451 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0651,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04452 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0197 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0651,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04453 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0245 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0245 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0651,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04454 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0651,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04455 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0991 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0536 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0991 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04456 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1429 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0536 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0536 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1429 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0537 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1163,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0537 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1163,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04459 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0537 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0246 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0246 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1163,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04460 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0537 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1163,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04461 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0992 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0537 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0992 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04462 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1430 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0537 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0537 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1430 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04463 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04464 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0538 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0779,
  ] at hbad
  tauto

end ErdosSzekeres

end
