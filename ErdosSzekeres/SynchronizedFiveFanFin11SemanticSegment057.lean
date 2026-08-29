module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment056

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 057. -/

theorem synchronizedFiveFanFin11Semantic_clause04105 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0079,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04106 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0079,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04107 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0079,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04108 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0079,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04109 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0494 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04110 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0494 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0079 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04111 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0494 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0494 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04112 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0079 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04113 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0495 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0166 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0143,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04114 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0495 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0143,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04115 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0495 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0205 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0143,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04116 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0495 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0143,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04117 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0950 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0950 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04118 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1388 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0495 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1388 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04119 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0166 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04120 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04121 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04122 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04123 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04124 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0496 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0271,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04125 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0496 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04126 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0496 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0496 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04127 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0166 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04128 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04129 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04130 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04131 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04132 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0497 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04133 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0952 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0952 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04134 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0497 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0497 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04135 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1390 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1390 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0527 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 3, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04136 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0166 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1039,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04137 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1039,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04138 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1039,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04139 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1039,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04140 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0498 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1039,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04141 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0953 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0498 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0953 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04142 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1391 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0498 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0498 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1391 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04143 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0055,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04144 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0168 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0055,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0055,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04146 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0055,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04147 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0499 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0055,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04148 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0499 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04149 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0499 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0499 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04150 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0087,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0087,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04152 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0087,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04153 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0087,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04154 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0087,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04155 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0500 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04156 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0087 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04157 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0087 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04158 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0087 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04159 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0500 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04160 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0087 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 6, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04161 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0500 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0500 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0087 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04162 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0151,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0151,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04164 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0151,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04165 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0151,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04166 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0151,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04167 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0956 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0501 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0956 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04168 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1394 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0501 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0501 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1394 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0167 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0279,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04170 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0171 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0279,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04171 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0184 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0279,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04172 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0279,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04173 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0502 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0279,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0502 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0279 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04176 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0502 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0502 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
