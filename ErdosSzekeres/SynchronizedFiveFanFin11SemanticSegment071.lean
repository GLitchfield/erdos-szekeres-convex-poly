module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment070

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 071. -/

theorem synchronizedFiveFanFin11Semantic_clause05113 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1125,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05114 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1125,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05115 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1125,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05116 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0614 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1066 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05117 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1066 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1125 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05118 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1066 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1066 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1125 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05119 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0614 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1507 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05120 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1507 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1507 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1125 chi).mpr
  have hright0 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05121 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1507 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1507 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1125 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05122 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1507 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1507 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1125 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause05123 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0614 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1507 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0614 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1507 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1125 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05124 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0421,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05125 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0421,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05126 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0269 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0269 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0421,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05127 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0615 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0407 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0421,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05128 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0615 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1067 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05129 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1508 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0615 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0615 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1508 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05130 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0677,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05131 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0677,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05132 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0225 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0677,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05133 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0677,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05134 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0616 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0677,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05135 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0616 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1068 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05136 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1509 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0616 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0616 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1509 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05137 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1189,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05138 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1189,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05139 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1189,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05140 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1189,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05141 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0617 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1069 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05142 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1510 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0617 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0617 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1510 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05143 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0805,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05144 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0805,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0805,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05146 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0805,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05147 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0805,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05148 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0618 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1070 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05149 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1070 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0805 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05150 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1511 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0618 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1511 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0618 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1511 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0618 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1511 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0805 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05152 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05153 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05154 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05155 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05156 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1317,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05157 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0619 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1071 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05158 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1512 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0619 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0619 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1512 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05159 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05160 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05161 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05162 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1573,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05164 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0620 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05165 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1573 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05166 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1072 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1072 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1573 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05167 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1513 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0620 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1513 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05168 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0620 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1513 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0620 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1513 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1573 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0621 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0453,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05170 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0621 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0275 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0275 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0453,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05171 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0621 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0413 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0413 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0453,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05172 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0621 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1073 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05173 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1514 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0621 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1514 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0621 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1514 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0621 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1514 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0453 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause05175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0709,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05176 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0709,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05177 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0225 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0709,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05178 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0276 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0709,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05179 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0709,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05180 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0622 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1074 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1074 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0709 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05182 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1515 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0622 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0622 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1515 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05183 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1221,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05184 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1221,
  ] at hbad
  tauto

end ErdosSzekeres

end
