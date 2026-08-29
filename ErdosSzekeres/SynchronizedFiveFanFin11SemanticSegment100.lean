module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment099

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 100. -/

theorem synchronizedFiveFanFin11Semantic_clause07194 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1252,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07195 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1252,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07196 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1321 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0878 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1321 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07197 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0878 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1321 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1252 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause07198 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0878 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0878 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1766 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07199 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07200 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07201 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07202 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07203 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07204 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0868,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07205 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1322 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0879 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1322 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07206 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0879 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07207 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0868 chi).mpr
  have hright0 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07208 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0868 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause07209 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0868 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause07210 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0879 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1767 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0879 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1767 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0868 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause07211 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1380,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07212 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1380,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07213 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1380,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07214 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1380,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07215 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1380,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07216 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1323 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0880 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07217 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1380 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07218 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1323 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1380 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause07219 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0880 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0880 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07220 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1768 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1380 chi).mpr
  have hright0 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07221 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07222 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07223 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07224 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07225 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07226 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0881 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07227 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1636 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause07229 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause07230 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause07231 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1324 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07232 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0881 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07233 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0881 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1769 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0881 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1769 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause07234 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0882 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0882 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0932,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07235 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1325 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0882 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0882 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1325 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07236 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0882 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0882 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1770 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07237 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0883 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0883 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1444,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07238 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0883 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0883 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1444,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0883 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0420 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0420 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0883 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1444,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07240 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1326 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0883 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0883 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1326 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07241 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0883 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0883 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1771 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07242 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0884 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1700,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07243 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0884 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1700,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07244 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0884 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1700,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0884 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1700,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07246 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0884 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1700,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07247 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1327 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0884 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07248 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0106 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0106 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1327 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1700 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07249 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1772 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0884 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0884 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1772 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07250 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1828,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07251 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1828,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07252 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1828,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07253 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1828,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07254 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1828,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07255 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0885 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07256 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1328 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07257 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause07258 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause07259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07260 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07261 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0885 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1328 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07262 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0885 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0885 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1773 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07263 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0886 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0886 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0964,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07264 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1329 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0886 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0886 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1329 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
