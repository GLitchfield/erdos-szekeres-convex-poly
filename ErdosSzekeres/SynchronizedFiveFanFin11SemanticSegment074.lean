module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment073

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 074. -/

theorem synchronizedFiveFanFin11Semantic_clause05329 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0640 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0640 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0409,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05330 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0640 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0259 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0640 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0409,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1092 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0640 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0640 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1092 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05332 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1533 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0640 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0640 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1533 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05333 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0665,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05334 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0665,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05335 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0665,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05336 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0665,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05337 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0641 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1093 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05338 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0641 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0641 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1534 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05339 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1534 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1534 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0665 chi).mpr
  have hright0 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 7, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05340 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0232 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1177,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05341 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1177,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05342 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1177,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05343 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0642 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1177,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05344 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0642 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1094 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05345 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1535 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0642 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0642 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1535 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05346 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0793,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05347 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0793,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05348 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0793,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05349 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0793,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05350 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0793,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05351 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0643 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1095 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05352 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1095 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0793 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05353 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1536 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0643 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1536 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05354 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0643 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1536 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0643 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1536 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0793 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause05355 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0233 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05356 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05357 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05358 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05359 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0644 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05360 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0644 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1096 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05361 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1096 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1305 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05362 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1537 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0644 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0644 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1537 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05363 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0234 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1561,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05364 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0235 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1561,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05365 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1561,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05366 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1561,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05367 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1561,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05368 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0645 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1097 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05369 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1097 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1561 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05370 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1097 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1097 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1561 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05371 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0645 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1097 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1097 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1561 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05372 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0645 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0645 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1538 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05373 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1538 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1538 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1561 chi).mpr
  have hright0 : chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05374 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0646 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0646 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05375 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0646 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0646 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05376 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0646 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0646 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05377 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0646 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0646 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1098 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05378 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1539 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0646 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0646 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1539 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05379 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05380 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05381 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05382 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05383 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05384 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0647 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1099 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05385 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0647 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1099 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1099 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0361 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05386 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0647 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0647 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1540 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05387 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1540 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1540 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0361 chi).mpr
  have hright0 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05388 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05389 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05390 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05391 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05392 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05393 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0648 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1100 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05394 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1100 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0617 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05395 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1100 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1100 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05396 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0648 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1541 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1541 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1541 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0617 chi).mpr
  have hright0 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05398 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1541 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1541 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0648 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1541 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0648 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1541 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause05400 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1129,
  ] at hbad
  tauto

end ErdosSzekeres

end
