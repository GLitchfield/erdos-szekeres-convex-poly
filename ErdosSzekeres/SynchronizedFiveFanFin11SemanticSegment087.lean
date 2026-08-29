module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment086

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 087. -/

theorem synchronizedFiveFanFin11Semantic_clause06265 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1114,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06266 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1114,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06267 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1114,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06268 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1210 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0761 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1210 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06269 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1210 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1114 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06270 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1651 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0761 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1651 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06271 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0761 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1651 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0761 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1651 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1114 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06272 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0762 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0762 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0410,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06273 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0762 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0343 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0762 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0410,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06274 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1211 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0762 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0762 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1211 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06275 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0666,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06276 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0666,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06277 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0666,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06278 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0666,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06279 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0763 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0666,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06280 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1212 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0763 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1212 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06281 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0763 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0763 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1652 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06282 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1178,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06283 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1178,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06284 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1178,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06285 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1178,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06286 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1178,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06287 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1213 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0764 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1213 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06288 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0764 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0764 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1653 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06289 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0794,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06290 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0794,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06291 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0794,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06292 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0794,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06293 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0794,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06294 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1214 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0765 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1214 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06295 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1214 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0794 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06296 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1214 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0794 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06297 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1214 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0794 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06298 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0765 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1654 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06299 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0765 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1654 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0765 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1654 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0794 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause06300 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1306,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06301 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1306,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1306,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06303 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1306,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06304 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0766 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1306,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06305 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1215 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0766 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1215 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06306 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1215 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1306 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06307 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0766 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0766 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1655 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06308 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06309 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06310 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06311 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06312 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06313 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06314 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1216 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0767 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06315 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1562 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06316 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06317 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06318 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06319 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1216 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06320 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1656 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0767 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1656 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06321 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1656 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1656 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1562 chi).mpr
  have hright0 : chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06322 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1656 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1656 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause06323 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0767 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1656 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0767 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1656 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1562 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause06324 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06325 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06326 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06327 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06328 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0768 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06329 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1217 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0768 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1217 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06330 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0768 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0768 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1657 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06331 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06332 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06333 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06334 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06335 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0769 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06336 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1218 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0769 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0769 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1218 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
