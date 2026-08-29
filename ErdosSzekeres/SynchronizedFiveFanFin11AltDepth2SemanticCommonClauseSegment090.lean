module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 090. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0555 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0555 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1017 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11080 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0601 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1063 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0601 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1063 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1140 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0678 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1140 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0817 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14228 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1168 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1168 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0062 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1209 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0747 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0747 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1209 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18250 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0840 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1302 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1116 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0886 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0886 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1348 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20618 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1381 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1381 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1432 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21277 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1403 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0941 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0941 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1403 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21978 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0230 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0231 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0233 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0236 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0238 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0242 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0251 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0253 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0257 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0267 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0426 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0428 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0432 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0442 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0230 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0231 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0233 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0236 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0238 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0242 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0251 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0253 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0257 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0267 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0426 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0428 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0432 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0442 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0462 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 4, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0376 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0369 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 4, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0345 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 4, 5, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0313 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 4, 5, 6} := by
    apply (fin11AltDepth2_strongSet_iff_mask0121 chi).mpr
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22030 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0267 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0268 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0269 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0273 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0274 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0275 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0279 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0280 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0281 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0285 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0484 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0485 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0486 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0490 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0494 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0267 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0268 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0269 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0273 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0274 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0275 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0279 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0280 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0281 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0285 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0484 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0485 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0486 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0490 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0494 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {5, 6, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1888 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 6, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1857 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 5, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1825 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 5, 6, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1633 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 5, 6, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1377 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 5, 6, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0865 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 5, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 5, 6, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 0 =
          {5, 6, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {0, 6, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {0, 5, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {0, 5, 6, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {0, 5, 6, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 5, 6, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {0, 5, 6, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22891 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0987 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0991 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1000 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1232 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0987 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0991 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1000 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1015 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1106 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1232 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 4, 6, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1115
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 6, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 6, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 6, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 6, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24155 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1091 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1359 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1088 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1089 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1091 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1094 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1163 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1359 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 6, 7, 8, 9}, 3, by decide, by decide, Or.inl ?_⟩
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
      | exact right_of_not_left _ h1
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0965
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 6, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 6, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24287 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1111 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1372 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1100 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1102 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1111 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1121 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1141 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1372 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 5, 8, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1337
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24811 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1168 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1173 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1178 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1193 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1228 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1298 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1168 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1173 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1178 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1193 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1228 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1298 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 5, 10}, 9, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1086
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 5, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24767 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1168 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1169 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1174 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1224 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1294 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1168 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1169 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1174 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1189 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1224 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1294 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 5, 6}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0126
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24869 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1170 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1172 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1184 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1234 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1304 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1170 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1172 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1184 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1199 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1234 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1304 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0670
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 4, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25089 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1183 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1185 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1187 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1221 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1256 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1326 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1183 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1185 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1187 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1221 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1256 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1326 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 7, 8, 10}, 6, by decide, by decide, Or.inl ?_⟩
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
      | exact right_of_not_left _ h2
      | exact right_of_not_left _ h3
      | exact right_of_not_left _ h4
      | exact h5
      | exact right_of_not_left _ h6
      | exact right_of_not_left _ h7
      | exact right_of_not_left _ h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact h12
      | exact h13
      | exact h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1422
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22294 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1420 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1426 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1432 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1453 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1509 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1635 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1420 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1426 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1432 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1453 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1509 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1635 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 4, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1055
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 4}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 4, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23632 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1507 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1508 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1522 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1537 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1572 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1768 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1507 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1508 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1522 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1537 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1572 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1768 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 4, 8, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0797
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 4, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25212 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1654 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1655 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1665 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1675 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1730 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1800 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1654 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1655 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1665 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1675 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1730 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1800 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 5, 9, 10}, 8, by decide, by decide, Or.inr ?_⟩
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
      | exact h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact right_of_not_left _ h6
      | exact h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact h10
      | exact h11
      | exact h12
      | exact h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1590
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25612 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1715 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1735 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1840 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1692 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1694 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1699 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1715 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1735 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1840 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 4, 6, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1370
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25698 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1702 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1714 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1744 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1849 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1702 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1703 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1708 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1714 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1744 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1849 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
      | exact h1
      | exact h2
      | exact h3
      | exact h4
      | exact h5
      | exact h6
      | exact h7
      | exact h8
      | exact right_of_not_left _ h9
      | exact right_of_not_left _ h10
      | exact right_of_not_left _ h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask0874
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00148 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00320 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00385 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01972 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02863 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03292 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03843 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03848 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03985 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05692 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06508 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06961 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08375 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0511 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0301 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0511 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0295,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09363 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0544 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0201 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0544 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1547,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10266 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0574 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0193 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0195 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0200 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0280 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0193 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0195 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0200 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0280 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0364 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0574 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10475 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0581 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0371 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0581 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0093,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11642 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0620 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0217 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0620 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0421,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12842 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0660 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0240 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0660 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13954 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0697 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0282 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0282 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0697 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0929,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0737 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0295 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0737 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0662,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16323 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0776 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0334 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0776 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1562,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17493 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0815 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0349 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0815 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18692 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0380 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0855 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19805 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0486 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0892 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1636,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20973 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0931 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0450 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0931 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00370 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0181 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0181 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00407 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0182 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0182 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00777 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0198 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00856 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0201 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02004 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0249 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02201 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0257 at hbad
  cases hcolor0 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02951 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0288 at hbad
  cases hcolor0 : chi ⟨1, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03994 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0332 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05231 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0383 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0383 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0390 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05615 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05866 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07893 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0494 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0494 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0580 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1504 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0580 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1504 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0061 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11600 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1542 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1542 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask0613 chi).mpr
  have hright0 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12657 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0653 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1577 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0653 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1577 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13159 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1594 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0670 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0670 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1594 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18112 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0835 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1759 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0835 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1759 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0572 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18919 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1786 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0862 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0862 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1786 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19941 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0896 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1820 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0896 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1820 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1828 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

end ErdosSzekeres

end
