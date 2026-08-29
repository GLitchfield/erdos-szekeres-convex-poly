module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 058. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08047 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0962 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0500 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0500 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0962 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10456 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0580 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1042 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0580 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1042 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0061 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12218 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1101 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0569 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12645 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1115 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0653 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1115 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0655 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0655 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1117 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16395 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0778 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0778 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1240 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0362 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1309 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0847 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0847 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1309 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0875 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0875 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1337 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1332 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19268 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1336 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1336 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0820 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21910 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0202 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0203 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0207 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0209 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0213 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0218 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0230 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0234 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0239 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0254 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0370 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0374 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0379 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0394 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0202 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0203 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0207 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0209 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0213 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0218 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0230 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0234 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0239 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0254 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0370 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0374 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0379 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0394 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0429 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 3, 4, 5, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0572 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 3, 4, 5, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0569 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 4, 5, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0565 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 3, 5, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0557 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 3, 4, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0541 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 3, 4, 5} := by
    apply (fin11AltDepth2_strongSet_iff_mask0061 chi).mpr
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21948 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0209 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0211 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0214 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0216 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0219 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0226 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0252 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0255 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0262 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0272 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0392 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0395 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0402 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0412 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0467 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0209 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0211 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0214 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0216 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0219 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0226 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0252 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0255 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0262 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0272 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0392 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0395 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0402 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0412 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0467 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {2, 4, 5, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1204 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 4, 5, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1201 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 2, 5, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1189 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 2, 4, 7, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1173 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 2, 4, 5, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1077 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 2, 4, 5, 7} := by
    apply (fin11AltDepth2_strongSet_iff_mask0181 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 2, 4, 5, 7, 10} : Finset (Fin 11))) :
      y ∈ ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 0 =
          {2, 4, 5, 7, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 2 =
          {0, 4, 5, 7, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 4 =
          {0, 2, 5, 7, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 5 =
          {0, 2, 4, 7, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 7 =
          {0, 2, 4, 5, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 2, 4, 5, 7, 10} : Finset (Fin 11)).erase 10 =
          {0, 2, 4, 5, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22311 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0959 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0960 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0971 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0992 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1174 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0959 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0960 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0971 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom0992 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1048 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1174 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 5, 6}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0111
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 5}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 3, 6}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 6}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 3, 5, 6}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 5, 6}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23209 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1264 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1008 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1010 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1017 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1027 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1138 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1264 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0691
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23943 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1338 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1066 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1067 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1077 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1087 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1142 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1338 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1589
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25379 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1208 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1209 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1211 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1220 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1285 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1355 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1208 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1209 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1211 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1220 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1285 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1355 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 8, 9}, 6, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0934
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25851 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1261 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1272 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1282 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1402 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1260 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1261 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1266 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1272 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1282 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1402 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 4, 5, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0882
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26121 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1297 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1298 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1308 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1318 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1338 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1373 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1297 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1298 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1308 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1318 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1338 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1373 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 5, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1596
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 3, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22424 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1424 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1425 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1445 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1466 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1522 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1648 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1424 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1425 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1445 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1466 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1522 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1648 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 3, 8, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0783
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 3, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22532 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1428 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1440 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1532 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1658 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1428 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1431 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1440 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1476 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1532 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1658 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 6, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0599
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23250 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1472 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1473 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1483 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1493 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1604 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1730 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1472 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1473 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1483 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1493 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1604 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1730 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1587
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24630 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1599 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1601 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1603 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1612 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1622 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1868 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1599 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1601 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1603 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1612 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1622 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1868 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 4, 5, 7, 8, 10}, 6, by decide, by decide, Or.inr ?_⟩
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
      | exact h2
      | exact h3
      | exact h4
      | exact right_of_not_left _ h5
      | exact h6
      | exact h7
      | exact h8
      | exact h9
      | exact h10
      | exact h11
      | exact right_of_not_left _ h12
      | exact right_of_not_left _ h13
      | exact right_of_not_left _ h14
  · intro polygon hsub hcard hstrong
    have heq := fin11AltDepth2_fiveSubset_mask1457
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24818 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1631 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1632 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1656 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1761 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1631 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1632 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1641 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1656 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1691 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1761 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 4, 6, 7}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0222
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 3, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 4, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25140 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1651 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1654 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1658 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1668 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1723 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1793 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1651 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1654 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1658 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1668 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1723 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1793 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 5, 6, 9}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0630
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01757 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01879 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02622 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03554 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03584 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03652 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0114 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05478 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05977 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05981 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07399 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07634 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07831 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07806 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08072 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0501 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0172 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0501 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0527,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09002 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0532 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0178 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0532 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0299,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0360 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0570 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0451,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11402 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0612 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0214 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0214 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0612 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1173,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12515 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0439 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0649 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1305,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13684 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0688 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0283 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0688 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14971 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0731 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0293 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0731 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1078,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15963 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0764 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0322 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0764 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0314,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17193 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0348 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0805 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18302 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0374 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0842 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19444 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0880 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0419 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0880 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0852,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20642 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0437 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0920 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00088 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0169 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0169 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00161 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01884 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0244 at hbad
  cases hcolor0 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01978 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0248 at hbad
  cases hcolor0 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02423 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0266 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0322 at hbad
  cases hcolor0 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04816 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0366 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04872 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0368 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05364 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07257 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0468 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07488 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0477 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0477 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07860 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0493 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0493 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09596 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0551 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0551 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1475 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0339 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1502 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0578 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0578 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1502 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11993 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0631 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1555 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0631 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1555 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15360 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0743 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1667 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0743 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1667 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0358 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause16129 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0769 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0769 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1693 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19350 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0876 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1800 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0876 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1800 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1588 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20990 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1855 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1855 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1832 chi).mpr
  have hright0 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
