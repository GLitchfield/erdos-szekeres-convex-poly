module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment071

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 072. -/

theorem synchronizedFiveFanFin11Semantic_clause05185 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1221,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05186 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1221,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05187 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1221,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05188 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0623 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1075 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05189 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1516 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0623 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0623 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1516 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05190 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0837,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0837,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05192 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0837,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05193 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0837,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05194 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0837,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05195 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0624 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05196 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1076 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0837 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05197 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1076 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0837 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05198 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1076 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0837 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05199 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1076 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1076 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0837 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05200 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1517 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0624 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1517 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05201 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0624 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1517 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0624 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1517 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0837 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05202 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1349,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05203 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1349,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05204 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1349,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05205 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1349,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05206 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1349,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05207 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0625 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1077 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05208 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1077 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1349 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05209 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1077 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1077 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1349 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05210 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1077 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1077 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1349 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05211 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0625 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05212 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0625 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1518 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0625 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1518 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1349 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05213 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1605,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05214 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1605,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05215 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1605,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05216 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1605,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05217 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1605,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05218 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0626 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05219 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1078 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1605 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05220 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1078 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05221 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1078 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05222 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1078 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1078 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05223 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0626 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05224 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1519 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1605 chi).mpr
  have hright0 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05225 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1519 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05226 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1519 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11Semantic_clause05227 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0626 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1519 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0626 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1519 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0627 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0627 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0901,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05229 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0627 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0627 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1079 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05230 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1520 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0627 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0627 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1520 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05231 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0224 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0224 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1413,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05232 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1413,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05233 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1413,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05234 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0628 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0282 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0282 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1413,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05235 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0628 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1080 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05236 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1521 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0628 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0628 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1521 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05237 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0225 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1669,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05238 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1669,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05239 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1669,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05240 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1669,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05241 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0629 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1669,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05242 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0629 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1081 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05243 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1522 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0629 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0629 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1522 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05244 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05246 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05247 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05248 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05249 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0630 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1082 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05250 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1082 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1797 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05251 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0630 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1082 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1082 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1797 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05252 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1523 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0630 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0630 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1523 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05253 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0230 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0121,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05254 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0231 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0121,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05255 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0236 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0121,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05256 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0631 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0121,
  ] at hbad
  tauto

end ErdosSzekeres

end
