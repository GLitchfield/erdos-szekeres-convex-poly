module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment057

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 058. -/

theorem synchronizedFiveFanFin11Semantic_clause04177 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0535,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04178 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0535,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04179 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0185 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0535,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04180 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0535,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0535,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04182 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0503 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04183 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0958 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0535 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04184 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0958 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0958 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0535 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause04185 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0503 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04186 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0535 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04187 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0503 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0503 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1396 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0535 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause04188 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1047,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04189 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1047,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04190 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1047,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1047,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04192 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1047,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04193 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0959 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0504 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0959 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04194 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0504 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0959 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0959 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1047 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04195 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1397 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0504 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0504 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1397 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04196 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1397 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1397 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1047 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04197 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04198 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04199 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04200 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04201 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04202 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0103,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04203 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0505 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04204 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0960 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0103 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04205 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0505 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0960 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0960 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0103 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04206 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0505 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0505 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04207 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1398 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1398 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0103 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04208 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0506 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0506 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0167,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04209 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0506 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0506 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0167,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04210 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0506 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0506 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0167,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04211 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0961 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0506 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0961 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04212 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1399 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0506 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0506 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1399 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04213 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04214 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04215 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04216 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04217 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04218 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0507 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0962 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04219 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1400 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0507 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0507 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1400 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04220 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0551,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04221 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0551,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04222 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0551,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04223 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0551,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04224 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0551,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04225 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0963 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0508 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0963 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04226 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0508 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0508 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04227 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1401 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1401 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0551 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04229 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04230 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04231 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04232 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04233 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0509 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1063,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04234 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0964 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0509 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0964 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04235 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0509 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0509 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04236 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1402 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1402 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1063 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04237 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0199,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04238 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0199,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0199,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04240 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0199,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04241 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0303 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0199,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04242 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0965 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0510 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0965 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04243 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0510 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0510 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1403 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04244 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04246 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04247 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04248 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0511 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0327,
  ] at hbad
  tauto

end ErdosSzekeres

end
