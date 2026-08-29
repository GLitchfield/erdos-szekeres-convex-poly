module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment107

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 108. -/

theorem synchronizedFiveFanFin11Semantic_clause07762 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0238 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0240 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0247 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0248 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1832 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1825 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1801 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1577 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1321 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0809 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {3, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {0, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 3, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 3, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07763 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0252 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0880 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0865 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0849 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0817 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0625 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0369 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 4, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 0 =
          {4, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {0, 4, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 4, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 4, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 4, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07764 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0250 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0253 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0264 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0268 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1648 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1633 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1617 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1585 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1137 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0625 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 4, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 0 =
          {4, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {0, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 4, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 4, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 4, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 4, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07765 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0255 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0257 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0259 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0262 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0275 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0276 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0278 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0281 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0467 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0473 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0487 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0275 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0281 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0473 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0487 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0976 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0961 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 4, 7, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0913 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0849 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0721 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 4, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0465 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 4, 6, 7, 8, 9} : Finset (Fin 11))) :
      y ∈ ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 0 =
          {4, 6, 7, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 4 =
          {0, 6, 7, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 6 =
          {0, 4, 7, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 7 =
          {0, 4, 6, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 8 =
          {0, 4, 6, 7, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 9} : Finset (Fin 11)).erase 9 =
          {0, 4, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07766 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0255 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0256 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0258 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0259 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0261 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0263 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0275 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0277 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0282 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0467 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0469 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0474 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0275 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0282 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0488 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {4, 6, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1488 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1473 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 4, 7, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1425 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1361 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 4, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1233 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 4, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0465 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 4, 6, 7, 8, 10} : Finset (Fin 11))) :
      y ∈ ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 0 =
          {4, 6, 7, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 4 =
          {0, 6, 7, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 6 =
          {0, 4, 7, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 7 =
          {0, 4, 6, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 8 =
          {0, 4, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 4, 6, 7, 8, 10} : Finset (Fin 11)).erase 10 =
          {0, 4, 6, 7, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07767 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0124 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 6} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 6} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07768 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0188 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0186 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0182 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0174 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0158 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 7} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 7} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07769 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0316 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0314 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0310 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0302 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0286 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07770 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0570 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0558 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07771 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1084 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1082 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1078 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1070 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1054 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 5} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0062 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 5, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 5, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 5, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 5, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 5, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 5, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 4, 5} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07772 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0348 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0346 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0342 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0334 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0286 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 4, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07773 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0604 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 6, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07774 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1116 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1114 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1110 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1054 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0094 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 6, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 6, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 4, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07775 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0370 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0668 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0666 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0662 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0654 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0158 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 4, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07776 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0796 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0794 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0782 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0286 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 4, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07777 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1564 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 4, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1054 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 4, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0542 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 4, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 4, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 4, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 4, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 4, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07778 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0375 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0236 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0234 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0230 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0206 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0174 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07779 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0364 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0362 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0334 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0302 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07780 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0620 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0558 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07781 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1132 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1130 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1126 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1070 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0110 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07782 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0812 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0810 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0806 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0782 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0558 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0302 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07783 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1580 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1578 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1070 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0558 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07784 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0716 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0714 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0710 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0654 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0206 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07785 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0330 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0361 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0379 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1228 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1226 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1222 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1166 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0206 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 7, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 7, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 7, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 7, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 7, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 7, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07786 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0844 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0842 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0838 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0782 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0334 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07787 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1356 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1354 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1350 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1294 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0334 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07788 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1612 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1102 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0590 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07789 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0288 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0330 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0383 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0384 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1676 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1674 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1166 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0654 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07790 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0291 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1804 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1802 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1798 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 3, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1550 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 3, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1294 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 3, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0782 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 3, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 3, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 3, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 3, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 3, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 3, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 3, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 3, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07791 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0244 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0242 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0230 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0214 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0182 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07792 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0372 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0370 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0342 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0310 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07793 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0628 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0626 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07794 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1140 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1138 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1126 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1110 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1078 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0118 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07795 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0307 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0343 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0353 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0397 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0407 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0307 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0397 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0436 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0434 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0422 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0406 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0310 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0182 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 7, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 7, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 7, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 7, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 7, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 7 =
          {1, 2, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07796 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0389 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0692 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0690 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0678 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0662 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0182 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07797 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0390 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0820 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0818 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0806 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0310 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07798 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0292 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0391 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0392 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1588 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1078 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0566 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07799 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0393 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0724 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0722 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0710 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0662 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0214 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {2, 4, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {1, 4, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07800 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0852 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0850 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0838 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0342 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {1, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07801 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0394 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1364 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1362 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1350 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1302 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1110 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0342 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07802 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0396 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1620 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1110 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0598 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07803 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0398 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0399 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1684 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1682 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1174 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0662 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07804 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0296 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0297 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0400 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0401 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1812 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1810 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1798 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1558 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1302 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0790 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 4, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 4, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 4, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 4, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 4, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 4, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07805 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0307 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0353 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0359 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0407 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0413 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0307 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0413 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0477 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0484 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0482 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0454 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 7, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0422 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0230 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 6, 7, 8} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 1 =
          {2, 5, 6, 7, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 2 =
          {1, 5, 6, 7, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 5 =
          {1, 2, 6, 7, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 6 =
          {1, 2, 5, 7, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 7 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 8} : Finset (Fin 11)).erase 8 =
          {1, 2, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07806 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0403 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0740 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0738 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0710 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0678 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0230 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {2, 5, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 2 =
          {1, 5, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 5, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07807 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0868 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0866 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0838 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0806 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {2, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 2 =
          {1, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {1, 2, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 2, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07808 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0404 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1380 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1378 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1350 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1318 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1126 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0358 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {2, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 2 =
          {1, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07809 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0406 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1636 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1634 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1126 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0614 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07810 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0299 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0355 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0408 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0409 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1700 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1698 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1190 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0678 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 5, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 5, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 5, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 5, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07811 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0410 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0412 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1828 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1826 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1798 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1574 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1318 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0806 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07812 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0303 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0308 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0309 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0361 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0414 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0415 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0421 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1732 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 6, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1730 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1670 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 6, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1222 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0710 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 6, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 6, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 6, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 6, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 6, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07813 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0305 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0306 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0310 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0311 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0312 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0418 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1860 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1858 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 2, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1798 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 2, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1606 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 2, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1350 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 2, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0838 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 2, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 2, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {2, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 2 =
          {1, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 2, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 2, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 2, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 2, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 2, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07814 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0248 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0242 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0234 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0218 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0186 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 6, 7} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 6, 7} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 6, 7} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 6, 7} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 6, 7} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 5, 7} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 7} : Finset (Fin 11)).erase 7 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07815 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0370 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0362 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0346 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0314 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 6, 8} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 6, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 6, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 6, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 6, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 5, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 8} : Finset (Fin 11)).erase 8 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07816 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0632 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0626 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0570 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 6, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 6, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 6, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07817 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0334 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1144 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1138 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1130 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1114 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1082 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 6} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0122 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 6, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 6, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 6, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 6, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 6, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 6, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 5, 6} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07818 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0335 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0424 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0696 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0690 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0682 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0666 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0570 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0186 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 3, 4, 5, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07819 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0336 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1336 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1330 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1322 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1306 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1082 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0314 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 5, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07820 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0313 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0337 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0338 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1592 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1586 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1578 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 5, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1082 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 5, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0570 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 5, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 5, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 5, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 5, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 5, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 5, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07821 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0339 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0428 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0728 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0722 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0714 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0666 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0218 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {3, 4, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {1, 4, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 4 =
          {1, 3, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07822 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0856 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0850 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0842 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0794 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0346 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {3, 4, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {1, 4, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 4 =
          {1, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07823 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0340 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1368 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1362 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1354 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1306 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1114 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0346 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07824 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0314 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0341 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0342 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1624 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1618 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1114 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0602 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07825 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0315 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0330 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0344 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0366 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0433 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0434 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1688 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1682 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 7, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1674 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 7, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1178 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0666 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 7, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 7, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 7, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 7, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 7 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 7, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 7, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 7, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07826 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0317 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0318 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0346 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0435 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1816 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 4, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1810 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1802 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 4, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1562 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 4, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1306 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 4, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0794 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 4, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 4, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 4, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 4 =
          {1, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 4, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 4, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 4, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 4, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07827 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0320 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0324 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0329 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0354 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0360 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0438 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0449 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0744 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0738 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0714 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 5, 7, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0682 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 5, 6, 7} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0234 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 5, 6, 7, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 1 =
          {3, 5, 6, 7, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 3 =
          {1, 5, 6, 7, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 5 =
          {1, 3, 6, 7, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 6 =
          {1, 3, 5, 7, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 7 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 7, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07828 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0872 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0866 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0842 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0810 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0362 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 5, 6, 8, 9} : Finset (Fin 11))) :
      y ∈ ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 1 =
          {3, 5, 6, 8, 9} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 3 =
          {1, 5, 6, 8, 9} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 5 =
          {1, 3, 6, 8, 9} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 6 =
          {1, 3, 5, 8, 9} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 8 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 9} : Finset (Fin 11)).erase 9 =
          {1, 3, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07829 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0439 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1384 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1378 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1354 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1322 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1130 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 5, 6, 8} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0362 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 5, 6, 8, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 1 =
          {3, 5, 6, 8, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 3 =
          {1, 5, 6, 8, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 6, 8, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 5, 8, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 8, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 5, 6, 8} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07830 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0352 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0441 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1640 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1634 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1578 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 5, 6, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1130 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 5, 6, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0618 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 5, 6, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 5, 6, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 5, 6, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 5, 6, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 6, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 5, 6, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07831 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0321 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0322 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0323 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0356 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0358 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1832 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 5, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1826 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1802 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 5, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1578 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 5, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1322 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 5, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0810 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 5, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 5, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 5, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {1, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 5, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 5, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 5, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 5, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11Semantic_clause07832 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0326 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0327 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0331 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0332 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0333 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0362 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0363 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0367 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0453 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1864 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {1, 6, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1858 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {1, 3, 8, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1802 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {1, 3, 6, 9, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1610 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {1, 3, 6, 8, 10} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask1354 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {1, 3, 6, 8, 9} := by
    apply (synchronizedFiveFanFin11_strongSet_iff_mask0842 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({1, 3, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 1 =
          {3, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 3 =
          {1, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {1, 3, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {1, 3, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {1, 3, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({1, 3, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {1, 3, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

end ErdosSzekeres

end
