module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment083

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 084. -/

theorem synchronizedFiveFanFin11Semantic_clause06049 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0358,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06050 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0358,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06051 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0358,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06052 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0358,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06053 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1185 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0735 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06054 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0358 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06055 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0358 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause06056 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1185 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0358 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06057 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0735 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06058 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1625 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0358 chi).mpr
  have hright0 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06059 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06060 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06061 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06062 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06063 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06064 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0614,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06065 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0736 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06066 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0614 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06067 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1186 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0614 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06068 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0736 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06069 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0614 chi).mpr
  have hright0 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06070 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0614 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06071 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0736 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1626 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0736 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1626 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0614 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06072 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1126,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06073 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1126,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06074 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1126,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06075 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1126,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06076 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1126,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06077 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0737 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06078 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1126 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06079 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1187 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1126 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06080 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0737 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0737 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1627 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06081 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0738 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0738 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0422,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06082 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0738 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0738 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0422,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06083 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1188 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0738 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0738 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1188 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06084 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0738 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0738 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1628 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06085 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0678,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06086 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0678,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06087 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0678,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06088 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0678,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06089 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0678,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06090 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0739 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1189 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06091 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0739 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0739 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1629 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06092 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1190,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06093 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1190,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06094 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1190,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06095 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1190,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06096 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1190 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0740 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1190 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06097 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0740 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0740 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1630 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06098 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06099 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06100 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06101 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06102 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0806,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06103 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1191 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0741 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1191 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06104 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0741 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0741 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1631 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06105 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06106 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06107 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06108 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06109 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06110 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1318,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06111 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1192 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0742 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1192 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06112 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1192 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1318 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06113 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0742 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0742 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1632 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06114 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1574,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06115 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1574,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06116 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1574,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06117 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1574,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06118 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1574,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06119 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0743 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06120 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1193 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1574 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end ErdosSzekeres

end
