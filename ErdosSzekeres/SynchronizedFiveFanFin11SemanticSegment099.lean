module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment098

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 099. -/

theorem synchronizedFiveFanFin11Semantic_clause07123 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0869 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0869 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1758 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07124 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1758 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1758 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0852 chi).mpr
  have hright0 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07125 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07126 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07127 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07128 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07129 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07130 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1313 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0870 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1313 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07131 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0870 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1759 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07132 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1759 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1759 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1364 chi).mpr
  have hright0 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07133 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0870 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1759 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0870 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1759 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1364 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause07134 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07135 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07136 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07137 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07138 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07139 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07140 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1314 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0871 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07141 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1620 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07142 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause07143 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07144 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1314 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07146 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0871 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1760 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07147 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1760 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1760 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1620 chi).mpr
  have hright0 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07148 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0871 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1760 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0871 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1760 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause07149 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0872 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0872 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0916,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07150 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0872 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0473 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0473 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0872 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0916,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1315 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0872 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0872 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1315 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07152 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0873 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0397 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0397 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07153 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0873 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07154 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0873 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07155 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0873 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0420 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0420 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07156 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0873 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07157 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1316 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0873 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1316 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07158 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0873 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0873 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1761 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07159 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07160 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07161 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07162 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0874 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07164 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1317 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0874 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1317 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07165 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1762 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0874 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0874 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1762 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07166 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07167 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07168 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07170 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07171 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1318 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0875 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07172 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1812 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07173 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1318 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0875 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1763 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07176 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1763 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1812 chi).mpr
  have hright0 : chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07177 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0875 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1763 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0875 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1763 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause07178 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0876 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0876 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0484,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07179 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0876 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0876 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0484,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07180 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1319 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0876 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0876 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1319 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0876 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0876 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1764 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07182 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0740,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07183 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0740,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07184 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0740,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07185 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0740,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07186 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0740,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07187 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1320 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0877 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1320 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07188 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1320 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0740 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07189 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0877 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1765 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07190 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0877 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1765 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0877 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1765 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0740 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause07191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1252,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07192 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1252,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07193 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1252,
  ] at hbad
  tauto

end ErdosSzekeres

end
