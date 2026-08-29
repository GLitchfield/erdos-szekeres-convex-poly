module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment106

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 107. -/

theorem synchronizedFiveFanFin11Semantic_clause07691 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0232 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0245 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0232 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0245 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0666 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0665 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0659 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0651 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0155 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 4, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07692 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0794 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0793 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0779 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0283 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 4, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07693 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0174 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1561 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1051 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0539 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 4, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 4, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 4, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 4, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07694 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0241 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0265 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0234 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0233 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0227 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0203 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0171 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0107 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07695 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0362 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0355 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0331 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0299 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0107 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07696 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0617 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0611 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0587 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0555 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0107 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07697 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0245 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0270 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0245 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0682 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0681 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0675 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0651 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0555 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0171 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07698 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1322 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1321 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1315 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1291 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1067 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0299 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07699 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0175 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1578 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1577 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1571 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1067 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0555 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07700 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0842 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0841 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0835 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0779 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0587 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0331 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 3, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 3, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 1, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07701 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1354 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1353 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1347 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1291 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1099 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0331 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07702 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0176 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1609 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1099 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0587 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07703 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0177 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0198 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0245 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0246 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0283 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0330 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0245 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0246 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1674 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1673 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1667 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1163 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0651 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07704 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0178 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0179 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0180 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0179 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0180 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1802 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1801 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1795 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1547 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1291 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0779 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 3, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 3, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 3, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 1, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 3, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 3, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 3, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07705 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0188 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0251 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0255 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0265 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0242 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0241 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0227 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0211 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0179 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07706 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0370 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0369 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0355 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0339 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0307 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07707 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0626 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0625 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0611 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0563 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07708 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1138 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1137 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1123 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1107 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1075 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0115 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07709 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0818 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0817 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0803 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0563 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0307 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07710 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0181 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0181 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1585 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1571 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1075 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0563 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07711 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0192 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0255 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0276 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0722 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0721 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0707 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0659 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0211 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 0 =
          {1, 4, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {0, 4, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07712 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0850 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0849 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0835 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0339 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {1, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {0, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 1, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07713 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1362 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1361 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1347 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1299 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1107 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0339 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07714 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0182 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0182 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1617 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1107 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0595 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07715 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0183 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0198 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0261 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0283 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0183 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1682 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1681 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1667 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1171 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0659 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07716 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0184 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0185 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0186 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0184 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0185 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1810 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1809 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1795 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1555 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1299 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0787 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 4, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 4, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 4, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 1, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 4, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 4, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 4, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07717 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1378 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1377 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1347 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1315 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1123 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0355 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 0 =
          {1, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {0, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07718 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1634 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1633 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1571 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1123 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0611 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07719 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0191 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1826 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1825 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1795 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1571 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1315 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0803 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 1, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07720 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0195 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0200 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {1, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1858 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1857 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 1, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1795 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 1, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1603 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 1, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1347 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 1, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0835 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 1, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 1, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {1, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {0, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 1, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 1, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 1, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 1, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 1, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07721 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0121 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0117 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0093 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0061 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 4, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07722 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0316 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0313 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0309 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0301 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0285 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0061 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 5, 8} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 5, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 5, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 5, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 5, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07723 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0569 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0061 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 5, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 5, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 5, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07724 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0348 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0345 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0341 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0333 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0285 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0093 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07725 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0601 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0597 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0589 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0093 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07726 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1116 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1113 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1109 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1101 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1053 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0093 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07727 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0796 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0793 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0781 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0285 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 4, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07728 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0202 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0202 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1561 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1557 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1549 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1053 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 4, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 4, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 4, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 4, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07729 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0205 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0241 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0265 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0236 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0233 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0229 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0205 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0173 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07730 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0364 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0357 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0333 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0301 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07731 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0617 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0613 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0589 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07732 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1129 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1125 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1101 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1069 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0109 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07733 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0205 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0237 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0245 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0270 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0245 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0684 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0681 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0677 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0653 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0173 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 2, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07734 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1324 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1321 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1317 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1293 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1069 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0301 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07735 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1577 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1573 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1549 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1069 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07736 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0844 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0841 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0837 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0781 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0589 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0333 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {2, 3, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 3, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07737 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0204 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1609 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1549 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1101 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0589 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07738 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0206 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0208 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1804 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1801 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1797 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1549 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1293 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0781 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 3, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 3, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 3, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 3, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 3, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 3, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07739 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0369 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0357 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0341 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0309 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0117 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07740 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0625 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0613 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0597 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0117 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07741 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1137 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1125 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1109 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1077 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0117 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07742 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0211 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0216 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0251 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0270 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0692 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0689 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0677 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0661 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0181 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07743 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0820 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0817 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0805 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0309 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07744 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1332 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1329 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1317 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1301 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1077 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0309 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07745 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0209 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1585 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1573 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1557 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1077 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07746 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0849 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0837 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0597 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0341 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07747 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1364 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1361 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1349 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1301 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1109 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0341 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07748 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0210 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1617 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1557 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1109 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0597 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07749 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0212 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0213 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0214 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0214 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1812 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1809 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1797 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1557 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1301 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0789 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 4, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07750 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0868 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0865 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0837 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0805 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0613 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0357 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {2, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {0, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 2, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 2, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 2, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07751 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0215 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1633 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1573 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1125 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0613 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07752 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0217 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0219 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1828 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1825 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1797 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1573 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1317 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0805 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07753 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0220 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0225 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0226 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0276 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0277 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0283 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0225 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1732 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1729 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1669 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1221 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0709 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07754 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0221 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0222 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0223 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0227 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0228 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0229 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1860 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1857 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1797 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1605 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1349 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0837 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {2, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {0, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 2, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 2, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07755 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0369 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0345 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0313 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0121 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 0 =
          {3, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {0, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {0, 3, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {0, 3, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {0, 3, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {0, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07756 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0625 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0617 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0601 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0569 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0121 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 0 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {0, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {0, 3, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {0, 3, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {0, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {0, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07757 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0230 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0230 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1144 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1137 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1129 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1113 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1081 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0121 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 0 =
          {3, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 3 =
          {0, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {0, 3, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {0, 3, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {0, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {0, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07758 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0233 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0233 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0856 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0849 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0841 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0793 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0601 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0345 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {3, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 3, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 3, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 3, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07759 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0231 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0234 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0235 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0231 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0234 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0235 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1617 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1609 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1561 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1113 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0601 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 3, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 3, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07760 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0242 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0865 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0841 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0809 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0617 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {3, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {0, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 3, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 3, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 3, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07761 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0236 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0243 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0244 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0236 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1633 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1609 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1577 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1129 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0617 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 3, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

end ErdosSzekeres

end
