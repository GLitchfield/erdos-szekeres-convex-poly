module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment105

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 106. -/

theorem synchronizedFiveFanFin11Semantic_clause07620 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07621 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07622 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0943 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07623 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1381 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0943 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07624 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1381 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1760 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07625 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0943 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0943 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1820 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07626 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07627 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07628 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07629 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07631 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1888,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07632 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1382 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0944 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07633 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1888 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0944 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1382 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1888 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause07635 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1821 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0944 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0944 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1821 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07636 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0945 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0945 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1952,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07637 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0945 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0491 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0491 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0945 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1952,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07638 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1383 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0945 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0945 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1383 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07639 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0945 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0945 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1822 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07640 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0946 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0946 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1984,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07641 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1384 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0946 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0946 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1384 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07642 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0061 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0059 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0055 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 4} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0031 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 5}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 4, 5} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 4, 5} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 4, 5} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 4} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07643 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0093 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0087 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 4} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0031 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 4, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 4, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 6} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 4} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07644 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0286 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0285 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0283 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0279 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0271 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 4} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0031 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 4, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 4, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 4, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 4, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 4, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 3, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 3, 4} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07645 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0527 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 4} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0031 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 4, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 4, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 3, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 3, 4} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07646 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1054 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1053 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1051 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1047 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1039 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 4} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0031 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 4, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 4, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 4, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 4, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 4, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 3, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 4, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 3, 4} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07647 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0107 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 5, 6} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 6} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07648 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0205 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0174 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0173 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0171 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0167 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0143 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 5, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 5, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 5, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 5, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 5, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07649 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0302 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0301 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0299 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0271 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 5, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 5, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 5, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 5, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07650 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0558 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0555 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0527 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 5, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 5, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 5, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 5, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07651 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1070 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1069 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1067 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1063 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1039 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0047 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 5, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 5, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 5, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 5, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 5, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 3, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 5, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 3, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07652 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0205 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0241 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0206 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0205 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0203 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0199 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0143 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07653 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0334 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0333 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0331 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0271 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07654 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0589 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0587 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0527 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07655 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1101 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1099 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1039 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0079 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 3, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 3, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07656 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0782 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0781 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0779 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0527 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0271 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 3, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 3, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07657 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1294 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1293 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1291 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1287 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1039 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0271 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 3, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 3, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07658 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0166 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1549 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 3, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1039 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 3, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0527 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 3, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 3, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 3, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 3, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 3, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07659 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0117 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0087 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0055 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 4, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 6} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07660 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0211 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0251 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0182 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0181 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0179 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0167 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0151 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0055 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 5, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 5, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 5, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 5, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 4, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07661 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0310 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0309 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0307 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0279 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0055 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 5, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 5, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 5, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 5, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07662 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0563 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0055 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 5, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 5, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 5, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07663 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0342 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0341 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0339 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0279 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0087 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07664 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0597 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0087 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07665 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1110 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1109 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1107 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1047 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0087 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07666 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0211 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0662 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0661 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0659 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0647 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0151 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07667 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0279 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07668 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0167 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0167 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1557 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1047 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0535 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 4, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 4, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 4, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 4, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07669 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0265 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0230 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0229 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0227 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0199 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0167 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07670 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0357 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0355 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07671 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0613 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0611 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07672 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1126 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1125 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1123 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1063 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0103 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07673 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0270 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0678 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0677 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0675 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0647 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0167 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07674 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0806 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0805 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0803 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07675 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1318 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1317 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1315 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1287 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1063 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0295 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07676 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0168 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1573 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1571 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1063 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0551 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07677 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0276 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0710 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0709 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0707 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0647 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0199 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07678 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0838 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0837 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0835 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 2, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 2, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 1, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07679 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1350 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1349 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1347 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1287 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0327 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07680 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0169 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0169 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1095 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0583 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07681 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0170 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0198 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0226 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0283 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0170 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1669 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1667 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1159 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0647 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07682 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0171 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0171 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1798 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1797 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1795 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 2, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1543 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 2, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1287 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 2, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0775 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 2, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 2, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 2, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 2, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 1, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 2, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 2, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 2, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 2, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07683 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0121 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0107 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0059 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 6} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07684 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0232 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0251 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0186 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0185 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0179 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0171 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0155 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0059 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 5, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 5, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 5, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 5, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 5, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 4, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07685 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0314 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0313 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0307 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0299 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0283 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0059 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 5, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 5, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 5, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 5, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 5, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07686 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0570 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0569 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0563 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0555 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0059 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 5, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 5, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 5, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 5, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 5, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 5, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07687 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0232 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0241 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0255 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0218 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0217 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0211 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0203 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0155 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 4, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07688 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0346 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0345 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0339 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0331 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0283 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07689 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0601 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0587 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07690 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1114 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1113 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1107 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1099 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1051 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0091 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

end ErdosSzekeres

end
