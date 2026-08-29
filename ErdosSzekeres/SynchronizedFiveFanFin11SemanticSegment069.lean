module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment068

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 069. -/

theorem synchronizedFiveFanFin11Semantic_clause04969 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0599 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1051 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04970 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1051 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0565 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04971 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1051 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1051 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0565 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04972 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1492 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0599 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1492 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04973 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1492 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1492 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0565 chi).mpr
  have hright0 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04974 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1492 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1492 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0565 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04975 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1077,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04976 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1077,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04977 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1077,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04978 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1077,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04979 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0392 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1077,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04980 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0600 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1052 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04981 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1052 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1052 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1077 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04982 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1493 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0600 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1493 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04983 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1493 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1493 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1077 chi).mpr
  have hright0 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04984 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0600 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1493 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0600 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1493 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1077 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04985 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0213,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04986 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0213,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04987 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0213,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04988 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0213,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04989 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0393 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0213,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04990 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0601 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1053 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04991 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0601 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0601 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1494 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04992 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1494 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0213 chi).mpr
  have hright0 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04993 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0341,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04994 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0341,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04995 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0341,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04996 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0341,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04997 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0341,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04998 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0602 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1054 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04999 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1054 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0341 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05000 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1054 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1054 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0341 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05001 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1054 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1054 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0341 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause05002 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1495 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0602 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1495 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05003 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0602 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0602 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1495 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0341 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause05004 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05005 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05006 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05007 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05008 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05009 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0597,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05010 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0603 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1055 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05011 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1055 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0597 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05012 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1055 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1055 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0597 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause05013 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1055 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1055 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0597 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05014 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1055 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1055 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0597 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05015 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0603 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0603 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1496 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05016 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05017 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05018 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05019 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05020 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05021 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0604 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1056 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05022 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1056 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1109 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05023 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1056 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1056 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05024 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1056 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1056 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05025 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1056 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1056 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05026 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0604 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05027 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1109 chi).mpr
  have hright0 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05028 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05029 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05030 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause05031 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0604 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0604 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1497 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1109 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05032 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0605 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0405,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05033 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0605 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0405,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05034 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0605 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0224 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0224 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0405,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05035 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0605 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0259 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0405,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05036 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1057 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0605 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1057 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05037 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0605 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0605 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1498 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05038 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0606 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0661,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05039 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0606 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0661,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05040 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0606 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0606 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0661,
  ] at hbad
  tauto

end ErdosSzekeres

end
