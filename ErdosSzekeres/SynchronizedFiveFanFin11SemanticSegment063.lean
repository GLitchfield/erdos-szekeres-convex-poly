module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment062

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 063. -/

theorem synchronizedFiveFanFin11Semantic_clause04537 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0211,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04538 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0339 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0211,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04539 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0546 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1001 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04540 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0546 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0546 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04541 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1439 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1439 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0211 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04542 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0339,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04543 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0339,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04544 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0339,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04545 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0339,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04546 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0339,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04547 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0547 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04548 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1002 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0339 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04549 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0547 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0547 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04550 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1440 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0339 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04551 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0595,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04552 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0595,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04553 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0595,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04554 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0595,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04555 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0595,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04556 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0548 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04557 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0595 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04558 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04559 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause04560 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1003 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1003 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04561 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0548 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04562 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1441 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0595 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04563 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04564 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause04565 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0548 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0548 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1441 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0595 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause04566 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04567 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04568 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04569 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04570 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1107,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04571 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0549 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04572 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1004 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1004 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1107 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04573 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0549 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0549 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04574 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1442 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1442 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1107 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04575 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0550 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0550 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0403,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04576 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0550 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0259 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0550 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0403,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04577 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0550 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0343 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0550 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0403,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04578 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0550 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0550 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1005 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04579 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1443 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0550 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0550 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1443 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04580 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0551 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0551 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0659,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04581 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0551 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0551 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0659,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04582 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0551 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0551 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0659,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04583 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0551 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0551 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1006 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04584 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1444 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0551 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0551 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1444 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04588 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04589 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0552 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1171,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04590 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0552 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0552 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1445 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04591 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0787,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04592 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0787,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04593 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0787,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04594 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0787,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0787,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04596 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1007 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04597 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1007 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0787 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04598 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0787 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04600 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0553 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0553 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1446 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0787 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04601 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04602 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04603 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04604 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04605 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0554 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04606 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0554 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1008 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04607 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1447 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0554 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0554 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1447 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04608 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1555,
  ] at hbad
  tauto

end ErdosSzekeres

end
