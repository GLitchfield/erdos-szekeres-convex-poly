module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment108

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 109. -/

theorem synchronizedFiveFanFin11Semantic_clause07833 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0343 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0353 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0359 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0461 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0467 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0496 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0482 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0466 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0434 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0370 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0242 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 6, 7, 8} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 1 =
          {4, 5, 6, 7, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 4 =
          {1, 5, 6, 7, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 5 =
          {1, 4, 6, 7, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 6 =
          {1, 4, 5, 7, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 7 =
          {1, 4, 5, 6, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 8 =
          {1, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07834 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0355 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0361 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0463 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1264 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1250 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1234 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1202 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1138 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0242 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 6, 7, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 1 =
          {4, 5, 6, 7, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 4 =
          {1, 5, 6, 7, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 5 =
          {1, 4, 6, 7, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 6 =
          {1, 4, 5, 7, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 7 =
          {1, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07835 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0866 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0850 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0818 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0626 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0370 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {1, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {1, 4, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 4, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07836 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1648 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1634 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1138 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0626 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {4, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07837 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0355 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0463 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1712 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1698 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1682 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1202 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0690 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {4, 5, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 5, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 4, 5, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 5, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07838 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1840 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1826 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1810 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1330 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0818 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {4, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 4, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07839 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0361 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1744 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1730 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1682 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1234 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0722 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {4, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 4, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07840 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1858 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1810 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1362 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0850 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 4, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {4, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 4, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 4, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07841 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0248 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0244 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0236 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0220 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0188 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07842 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0364 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0348 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0316 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07843 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07844 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1144 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1116 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1084 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07845 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0696 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0692 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0684 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0668 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0188 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07846 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0824 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0820 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0812 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0796 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0316 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07847 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1592 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1084 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07848 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0728 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0724 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0716 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0668 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0220 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {3, 4, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {2, 4, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {2, 3, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07849 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0856 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0844 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0796 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0348 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {3, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {2, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07850 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1368 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1364 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1356 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1308 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1116 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0348 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {2, 3, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07851 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1116 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07852 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0399 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0434 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1688 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1684 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1676 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1180 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0668 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07853 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1816 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1812 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1804 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1308 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0796 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 4, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 4, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 4, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 4, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 4, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07854 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0744 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0740 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0716 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0684 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0236 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {3, 5, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {2, 5, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 5 =
          {2, 3, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {2, 3, 5, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07855 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1256 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1252 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1228 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1196 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0236 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 6, 7, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 2 =
          {3, 5, 6, 7, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 3 =
          {2, 5, 6, 7, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 6, 7, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 5, 7, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 7 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 7, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07856 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0868 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0844 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0812 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0364 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {3, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {2, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {2, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {2, 3, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {2, 3, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07857 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1384 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1380 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1356 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1324 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0364 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {3, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {2, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07858 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07859 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1704 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1700 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1676 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1196 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0684 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 5, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 5, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 5, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 5, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07860 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1832 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1828 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1804 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1324 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0812 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07861 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1736 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1732 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1676 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1228 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0716 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07862 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1864 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1860 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1804 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1356 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0844 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 3, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 3, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {3, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {2, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 3, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 3, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07863 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0397 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0407 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0413 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0461 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0467 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0397 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0413 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0496 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0484 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0468 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0436 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0244 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 7, 8} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 7, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 7, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 7, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 7, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 7 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 8} : Finset (Fin 11)).erase 8 =
          {2, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07864 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0752 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0740 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0724 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0692 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0244 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {2, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07865 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0399 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0463 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1264 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1252 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1236 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1204 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0244 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 7, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 7, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 7, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 7, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 7, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 7 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 7, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07866 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0868 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0820 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07867 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1392 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1380 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1364 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1332 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07868 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1648 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {4, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07869 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0399 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0463 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1712 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1700 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1684 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1204 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0692 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {4, 5, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 5, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 4, 5, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 5, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07870 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1840 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1828 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1812 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1332 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0820 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {4, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 4, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07871 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0399 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1744 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1732 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1684 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1236 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0724 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {4, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 4, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07872 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1860 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1812 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1364 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 4, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {4, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {2, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 4, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07873 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1760 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1732 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1700 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1252 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0740 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 5, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {5, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 5, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 5, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 5, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07874 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1888 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {2, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1860 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {2, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1828 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {2, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1380 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {2, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0868 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{2, 5, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({2, 5, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {5, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {2, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {2, 5, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {2, 5, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({2, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {2, 5, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07875 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0752 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0744 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0728 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0696 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0248 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {4, 5, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {3, 5, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 5 =
          {3, 4, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {3, 4, 5, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {3, 4, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07876 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0872 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0856 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0824 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {3, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {3, 4, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {3, 4, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {3, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07877 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1392 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1384 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1368 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1336 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1144 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {4, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {3, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {3, 4, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {3, 4, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {3, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07878 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1648 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1592 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1144 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {3, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07879 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0434 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0463 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1712 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1704 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1688 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1592 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1208 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0696 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 5, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 5, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {3, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {3, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 5, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 5, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07880 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1840 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1832 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1816 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1592 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1336 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0824 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {3, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {3, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07881 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0434 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1744 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1736 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1688 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1240 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0728 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {3, 4, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07882 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1864 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1816 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1368 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0856 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 4, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {4, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {3, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {3, 4, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 4, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 4, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 4, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07883 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0442 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0448 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0454 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0477 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0484 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0448 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0454 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0484 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1504 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 6, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1480 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 5, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1448 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1384 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1256 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0488 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 5, 6, 7, 8, 10} : Finset (Fin 11))) :
      y ∈ ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 3 =
          {5, 6, 7, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 5 =
          {3, 6, 7, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 6 =
          {3, 5, 7, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 7 =
          {3, 5, 6, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 8 =
          {3, 5, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 8, 10} : Finset (Fin 11)).erase 10 =
          {3, 5, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07884 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1760 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1736 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1704 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 5, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1256 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0744 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 5, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {5, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {3, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {3, 5, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 5, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 5, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07885 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1888 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {3, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1864 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {3, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1832 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {3, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1384 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {3, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0872 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{3, 5, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({3, 5, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {5, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {3, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {3, 5, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {3, 5, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({3, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {3, 5, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07886 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0457 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0461 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0467 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0473 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0477 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0483 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0487 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0473 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0483 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0487 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0992 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {4, 6, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0976 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {4, 5, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0944 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {4, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0752 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {4, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0496 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({4, 5, 6, 7, 8, 9} : Finset (Fin 11))) :
      y ∈ ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 4 =
          {5, 6, 7, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 5 =
          {4, 6, 7, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 6 =
          {4, 5, 7, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 7 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 8 =
          {4, 5, 6, 7, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 7, 8, 9} : Finset (Fin 11)).erase 9 =
          {4, 5, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07887 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1888 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {4, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1872 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {4, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1840 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {4, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1648 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {4, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1392 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({4, 5, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {5, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {4, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {4, 5, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {4, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {4, 5, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({4, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07888 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1149 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1027 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1149 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 5}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0063
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 5}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07889 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0948 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1149 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0948 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0954 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0975 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1027 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1149 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 5}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0063
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 5}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07890 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1468 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1589 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1468 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1589 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 5}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0063
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 5}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07891 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1386 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1392 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1413 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1468 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1589 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1386 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1392 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1413 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1468 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1589 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 5}, 10, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0063
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 5}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 5}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 5}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07892 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1150 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07893 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1469 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1590 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1469 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1590 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07894 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1150 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 8, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07895 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1150 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 9, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07896 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1469 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1590 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1469 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1590 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07897 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0949 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0955 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0976 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1150 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0949 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0955 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0976 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1028 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 10, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07898 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1387 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1393 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1414 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1469 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1590 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1387 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1393 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1414 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1469 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1590 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 6}, 10, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0095
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07899 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1152 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1030 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1152 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 5, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07900 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1591 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1471 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1591 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 5, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07901 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1152 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1030 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1152 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 6, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07902 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0947 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0951 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0957 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0978 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1152 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom0947 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom0951 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom0957 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom0978 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1030 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1152 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 9, by decide, by decide, Or.inl ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11Semantic_clause07903 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1385 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1389 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1395 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1416 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1471 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1591 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at h0
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at h1
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at h2
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at h3
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at h4
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at h5
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at h6
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at h7
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at h8
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at h9
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at h10
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at h11
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at h12
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at h13
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at h14
  unfold SynchronizedFiveFanFin11SemanticAtom1385 at h15
  unfold SynchronizedFiveFanFin11SemanticAtom1389 at h16
  unfold SynchronizedFiveFanFin11SemanticAtom1395 at h17
  unfold SynchronizedFiveFanFin11SemanticAtom1416 at h18
  unfold SynchronizedFiveFanFin11SemanticAtom1471 at h19
  unfold SynchronizedFiveFanFin11SemanticAtom1591 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 8}, 9, by decide, by decide, Or.inr ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, ?_⟩
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_assoc] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals
      simp at hnotLower hnotUpper ⊢
    all_goals first
      | exact right_of_not_left _ h0
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := synchronizedFiveFanFin11_fiveSubset_mask0287
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

end ErdosSzekeres

end
