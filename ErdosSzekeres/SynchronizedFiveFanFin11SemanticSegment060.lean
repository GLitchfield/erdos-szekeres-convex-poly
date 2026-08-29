module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment059

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 060. -/

theorem synchronizedFiveFanFin11Semantic_clause04321 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0520 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04322 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0059 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04323 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0091,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04324 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0091,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04325 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0091,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04326 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0091,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04327 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0091,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04328 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0521 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04329 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0091 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04330 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0521 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0521 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0521 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0091 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04332 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04333 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04334 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04335 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04336 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0155,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04337 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0977 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0522 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0977 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04338 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1415 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0522 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0522 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1415 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04339 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04340 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04341 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04342 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04343 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0283,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04344 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0523 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04345 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0523 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0523 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04346 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0283 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04347 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04348 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04349 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04350 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04351 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04352 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0979 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0524 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04353 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0979 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0979 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0539 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04354 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0524 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04355 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1417 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0539 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04356 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0524 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0524 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1417 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0539 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause04357 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04358 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04359 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04360 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04361 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1051,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04362 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0980 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0525 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0980 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04363 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1418 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0525 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1418 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04364 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1418 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1418 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1051 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04365 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0525 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0525 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1418 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1051 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04366 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04367 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04368 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04369 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04370 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04371 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04372 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0981 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0526 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0981 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04373 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0526 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04374 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1419 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0107 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04375 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0107 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause04376 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0526 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0526 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1419 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0107 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04377 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04378 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04379 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0237 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04380 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04381 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0982 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0527 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0982 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04382 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1420 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0527 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0527 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1420 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04383 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04384 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04385 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04386 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04387 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04388 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0983 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0528 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0983 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04389 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0528 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0528 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04390 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1421 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1421 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0299 chi).mpr
  have hright0 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04391 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04392 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0529 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0555,
  ] at hbad
  tauto

end ErdosSzekeres

end
