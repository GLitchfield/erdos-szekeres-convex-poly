module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment077

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 078. -/

theorem synchronizedFiveFanFin11Semantic_clause05617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05618 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05619 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05620 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0679 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05621 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1617 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05622 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause05623 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05624 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1131 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05625 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1572 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0679 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1572 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05626 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0680 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0913,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05627 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0680 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0680 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1132 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05628 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0259 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05629 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05631 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0282 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0282 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05632 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05633 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0681 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1133 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1573 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0681 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0681 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1573 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05635 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05636 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05637 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05638 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05639 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05640 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0682 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1134 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05641 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0682 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0682 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1574 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05642 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05643 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05644 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05645 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05646 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05647 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0683 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1135 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05648 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1135 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1809 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05649 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1135 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1135 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1809 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05650 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1575 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0683 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0683 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1575 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05651 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0684 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0481,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05652 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0684 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0481,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05653 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0684 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0481,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05654 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0684 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0684 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1136 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05655 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1576 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0684 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0684 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1576 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05656 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0737,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05657 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0737,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05658 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0737,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05659 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0276 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0737,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05660 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0737,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05661 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0685 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1137 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05662 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1577 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0685 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0685 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1577 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05663 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1249,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05664 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1249,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05665 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1249,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05666 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1249,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05667 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1249,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05668 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0686 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1138 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05669 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1578 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0686 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0686 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1578 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05670 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0865,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05671 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0865,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05672 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0865,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05673 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0865,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05674 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0865,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05675 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0687 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1139 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05676 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1139 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0865 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05677 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0687 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0687 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05678 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1579 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1579 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0865 chi).mpr
  have hright0 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05679 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1377,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05680 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1377,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05681 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1377,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05682 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1377,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05683 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1377,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05684 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1140 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0688 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1140 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05685 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1580 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0688 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0688 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1580 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05686 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1633,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05687 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1633,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05688 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1633,
  ] at hbad
  tauto

end ErdosSzekeres

end
