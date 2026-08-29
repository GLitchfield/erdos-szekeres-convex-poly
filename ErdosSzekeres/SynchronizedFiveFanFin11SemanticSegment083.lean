module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment082

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 083. -/

theorem synchronizedFiveFanFin11Semantic_clause05977 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05978 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05979 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05980 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0727 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05981 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1110 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05982 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05983 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05984 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05985 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05986 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1617 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0727 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05987 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05988 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause05989 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0727 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1617 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0727 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1617 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1110 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause05990 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0406,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05991 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0406,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05992 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0307 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0307 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0406,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05993 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0343 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0406,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05994 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0397 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0397 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0406,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05995 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1178 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1178 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05996 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1618 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0728 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1618 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05997 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0662,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05998 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0662,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05999 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0662,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06000 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0662,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06001 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1179 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0729 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1179 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06002 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1179 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1179 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0662 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06003 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1619 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0729 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0729 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1619 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06004 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06005 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06006 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06007 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06008 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06009 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1180 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0730 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1180 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06010 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1620 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0730 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0730 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1620 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06011 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0790,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06012 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0790,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06013 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0790,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06014 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0790,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06015 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0790,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06016 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0731 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06017 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1181 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0790 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06018 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1621 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0731 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1621 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06019 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0731 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1621 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0731 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1621 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0790 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause06020 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06021 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06022 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06023 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06024 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06025 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0732 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06026 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1302 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06027 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1182 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1302 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06028 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1622 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0732 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0732 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1622 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06029 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06030 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06031 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06032 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06033 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06034 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0733 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06035 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1558 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06036 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06037 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06038 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06039 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1183 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1183 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06040 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0733 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06041 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1623 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1558 chi).mpr
  have hright0 : chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06042 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0733 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1623 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0733 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1623 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06043 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0734 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0734 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0230,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06044 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0734 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0734 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0230,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06045 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0734 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0734 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0230,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06046 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1184 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0734 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0734 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1184 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06047 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1624 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0734 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0734 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1624 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06048 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0735 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0358,
  ] at hbad
  tauto

end ErdosSzekeres

end
