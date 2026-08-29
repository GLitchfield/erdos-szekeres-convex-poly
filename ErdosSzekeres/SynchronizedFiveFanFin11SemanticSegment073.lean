module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment072

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 073. -/

theorem synchronizedFiveFanFin11Semantic_clause05257 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0121,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05258 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0631 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05259 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0121 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05260 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1083 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0121 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05261 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1083 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1083 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0121 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause05262 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0631 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1524 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05263 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1524 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1524 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0121 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause05264 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0632 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0185,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05265 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0632 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0185,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05266 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0632 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0632 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0185,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05267 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0632 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0632 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1084 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05268 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1525 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0632 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0632 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1525 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05269 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0313,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05270 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0313,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05271 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0313,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05272 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0313,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05273 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0313,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05274 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0633 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1085 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05275 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0633 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0633 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1526 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05276 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0569,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05277 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0569,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05278 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0569,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05279 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0569,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05280 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0569,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05281 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0634 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1086 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05282 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0634 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0634 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1527 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05283 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1527 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1527 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0569 chi).mpr
  have hright0 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05284 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1081,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05285 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1081,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05286 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1081,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05287 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1081,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05288 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1081,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05289 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0635 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1087 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05290 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1528 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0635 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0635 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1528 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05291 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0217,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05292 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0217,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05293 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0217,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05294 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0217,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05295 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0636 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1088 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05296 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1529 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0636 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0636 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1529 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05297 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0345,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05298 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0345,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05299 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0345,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05300 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0345,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05301 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0345,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0637 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05303 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0345 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05304 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1089 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1089 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0345 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05305 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1530 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0637 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1530 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05306 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0637 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1530 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0637 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1530 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0345 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05307 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05308 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05309 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05310 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05311 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05312 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0638 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05313 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05314 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause05315 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11Semantic_clause05316 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause05317 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05318 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1090 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05319 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1531 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0638 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1531 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05320 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0638 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1531 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0638 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1531 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0601 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05321 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1113,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05322 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1113,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05323 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1113,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05324 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1113,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05325 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1113,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05326 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0639 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1091 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05327 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1532 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0639 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0639 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1532 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05328 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0640 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0640 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0409,
  ] at hbad
  tauto

end ErdosSzekeres

end
