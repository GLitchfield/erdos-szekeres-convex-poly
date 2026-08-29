module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment058

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 059. -/

theorem synchronizedFiveFanFin11Semantic_clause04249 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04250 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0511 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04251 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0966 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0966 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0327 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04252 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1404 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0511 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04253 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1404 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0327 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause04254 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0583,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04255 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0583,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04256 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0583,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04257 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0583,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04258 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0583,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0512 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04260 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0967 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0967 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0583 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04261 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0512 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0512 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04262 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1405 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1405 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0583 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04263 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04264 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04265 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04266 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04267 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1095,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04268 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0968 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0513 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0968 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04269 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0513 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04270 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1406 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1095 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04271 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0513 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0513 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1406 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1095 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04272 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0514 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0391,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04273 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0514 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0391,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04274 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0514 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0224 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0224 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0391,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04275 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0514 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0307 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0307 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0391,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04276 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0969 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0514 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0969 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04277 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1407 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0514 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0514 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1407 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04278 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0647,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04279 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0647,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04280 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0225 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0647,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04281 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0647,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04282 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0970 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0515 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0970 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04283 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1408 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0515 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0515 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1408 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04284 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1159,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04285 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1159,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04286 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1159,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04287 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1159,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04288 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1159,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04289 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0971 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0516 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0971 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04290 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1409 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0516 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0516 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1409 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04291 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04292 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04293 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04294 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04295 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04296 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0517 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0775,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04297 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0972 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0517 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0972 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04298 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1410 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0517 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0517 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1410 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04299 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1287,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04300 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1287,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04301 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1287,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1287,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04303 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1287,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04304 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0973 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0518 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0973 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04305 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1411 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0518 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0518 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1411 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04306 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1543,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04307 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1543,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04308 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1543,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04309 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1543,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04310 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1543,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04311 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0519 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04312 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0974 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0974 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1543 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04313 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0519 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0519 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04314 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1412 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1412 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1543 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04315 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0059,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04316 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0059,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04317 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0059,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04318 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0059,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04319 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0059,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04320 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0520 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0520 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
