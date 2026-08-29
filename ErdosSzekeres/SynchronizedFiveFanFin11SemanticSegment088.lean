module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment087

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 088. -/

theorem synchronizedFiveFanFin11Semantic_clause06337 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0769 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1658 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06338 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06339 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06340 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06341 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06342 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06343 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06344 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0770 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1219 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06345 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1219 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06346 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0770 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06347 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0770 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1659 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0770 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1659 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06348 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1130,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06349 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1130,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06350 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1130,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06351 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1130,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06352 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1130,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06353 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1220 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0771 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1220 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06354 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1220 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1130 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06355 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1660 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0771 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06356 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0771 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1660 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0771 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1660 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1130 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06357 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0772 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0772 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06358 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0772 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0772 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06359 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1221 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0772 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0772 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1221 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06360 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1661 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0772 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0772 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1661 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06361 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06362 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06363 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06364 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0773 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06365 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1222 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0773 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1222 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06366 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1662 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0773 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0773 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1662 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06367 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1194,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06368 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1194,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06369 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1194,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06370 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1194,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06371 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0774 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1194,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06372 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1223 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0774 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1223 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06373 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0774 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0774 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06374 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1663 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1663 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1194 chi).mpr
  have hright0 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06375 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06376 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06377 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06378 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06379 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06380 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1224 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0775 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1224 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06381 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0775 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06382 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1664 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0810 chi).mpr
  have hright0 : chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06383 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0775 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1664 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0775 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1664 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0810 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06384 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1322,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06385 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1322,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06386 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1322,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06387 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1322,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06388 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1322,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06389 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1225 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0776 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1225 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06390 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0776 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0776 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1665 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06391 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1578,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06392 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1578,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06393 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1578,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06394 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1578,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06395 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1578,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06396 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1226 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0777 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1226 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1226 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1226 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1578 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06398 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1666 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0777 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0777 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1666 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0777 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1666 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1578 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06400 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0778 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0359 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0778 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0458,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06401 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1667 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0778 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0778 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1667 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06402 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0714,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06403 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0714,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06404 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0714,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06405 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0779 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0714,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06406 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1227 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0779 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1227 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06407 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1668 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0779 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0779 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1668 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06408 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0780 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0780 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1226,
  ] at hbad
  tauto

end ErdosSzekeres

end
