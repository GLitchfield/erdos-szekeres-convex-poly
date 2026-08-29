module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Varying alternate-depth-two clauses, segment 043. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08678 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0983 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0983 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask0775 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08804 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0525 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0987 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0525 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0987 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0091 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09947 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1025 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0563 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1025 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1123 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10728 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1051 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0589 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1051 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0557 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11260 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0607 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1069 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0607 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1069 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0341 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11806 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0625 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0625 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1087 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1573 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12496 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0648 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0648 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1110 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0793 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13426 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1141 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0679 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1141 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1329 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14506 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0715 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1177 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0558 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15668 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1216 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1216 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_cupSet_iff_mask1222 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15766 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0757 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0757 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1219 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17296 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0808 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1270 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0722 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18730 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0856 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1318 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1580 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19813 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0892 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0892 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1354 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1636 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21040 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0933 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0933 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1395 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1480 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21997 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0236 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0237 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0238 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0241 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0242 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0245 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0266 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0267 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0270 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0276 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0441 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0442 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0445 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0451 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0236 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0237 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0238 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0241 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0242 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0245 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0266 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0267 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0270 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0276 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0441 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0442 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0445 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0451 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0481 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {3, 5, 6, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0488 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {0, 5, 6, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0481 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {0, 3, 6, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0457 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {0, 3, 5, 7, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0425 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {0, 3, 5, 6, 8} := by
    apply (fin11AltDepth2_strongSet_iff_mask0361 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {0, 3, 5, 6, 7} := by
    apply (fin11AltDepth2_strongSet_iff_mask0233 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({0, 3, 5, 6, 7, 8} : Finset (Fin 11))) :
      y ∈ ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 0 =
          {3, 5, 6, 7, 8} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 3 =
          {0, 5, 6, 7, 8} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 5 =
          {0, 3, 6, 7, 8} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 6 =
          {0, 3, 5, 7, 8} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 7 =
          {0, 3, 5, 6, 8} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({0, 3, 5, 6, 7, 8} : Finset (Fin 11)).erase 8 =
          {0, 3, 5, 6, 7} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23423 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1286 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1026 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1028 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1030 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1039 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1160 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1286 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 7, 8, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1443
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23969 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1068 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1340 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1068 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1070 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1073 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1089 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1144 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1340 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 6, 7, 9}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0725
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24033 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1073 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1096 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1347 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1073 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1074 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1077 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1096 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1151 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1347 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 7, 9, 10}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1685
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 4, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25067 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1181 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1182 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1188 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1219 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1324 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1181 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1182 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1188 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1219 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1254 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1324 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 3, 6, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1614
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25123 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1189 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1191 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1205 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1330 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1189 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1191 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1195 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1205 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1260 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1330 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 5, 6, 8}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0374
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 6, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 6, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 6, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25165 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0114 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1190 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1192 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1209 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1334 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0114 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1190 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1192 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1199 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1209 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1264 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1334 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 4, 5, 7, 9}, 3, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0694
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25353 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1205 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1207 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1212 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1218 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1283 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1353 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1205 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1207 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1212 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1218 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1283 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1353 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 6, 8, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1382
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25745 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1257 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1287 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1392 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1244 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1245 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1248 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1257 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1287 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1392 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 7, 9, 10}, 2, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1706
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 5, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25771 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1252 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1255 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1289 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1394 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1249 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1250 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1252 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1255 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1289 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1394 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 6, 7, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0970
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {1, 3, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 7, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 6, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 7, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 6, 7, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26443 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1333 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1335 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1337 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1406 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1333 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1335 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1337 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1346 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1356 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1406 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 4, 5, 7, 8, 10}, 0, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1460
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {2, 4, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 4, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {2, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26709 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0146 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0148 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1376 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1382 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1411 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0146 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1375 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1376 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1379 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1382 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1396 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1411 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{3, 4, 6, 7, 9, 10}, 5, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1752
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 6, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 7, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 6, 7, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 6, 7, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22510 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1428 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1429 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1438 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1474 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1530 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1656 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1428 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1429 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1438 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1474 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1530 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1656 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 6, 7}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0215
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22562 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1429 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1431 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1443 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1479 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1535 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1661 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1429 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1431 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1443 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1479 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1535 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1661 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 4, 7, 9}, 10, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0663
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 4, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 2, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 4, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22956 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1484 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1575 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1701 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1454 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1455 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1459 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1484 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1575 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1701 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 5, 6, 7}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0235
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 5, 7}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 5, 6, 7}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 7}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23368 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1484 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1486 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1489 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1495 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1616 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1742 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0131 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0141 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1484 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1486 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1489 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1495 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1616 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1742 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 7, 9}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0739
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23920 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1529 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1536 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1546 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1601 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1797 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1526 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1529 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1536 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1546 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1601 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1797 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 7, 10}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1205
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23910 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1526 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1528 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1535 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1545 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1600 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1796 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1526 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1528 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1535 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1545 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1600 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1796 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 4, 5, 7, 9}, 8, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0693
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 4, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 5, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 5, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24518 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0018 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0027 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0111 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1585 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1587 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1589 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1592 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1626 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1857 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0018 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0027 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0111 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0139 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1585 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1587 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1589 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1592 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1626 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1857 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 6, 7, 8, 10}, 4, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1481
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 6, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 6, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25392 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1670 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1672 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1674 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1748 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1818 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0151 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1670 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1672 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1674 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1683 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1748 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1818 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 2, 5, 7, 8, 10}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1446
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 2, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 5, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25674 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1706 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1712 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1742 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1847 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1701 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1703 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1706 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1712 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1742 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1847 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 7, 9}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0746
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 7, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 7, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 7, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25704 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1702 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1715 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1745 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1850 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0031 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1702 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1704 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1709 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1715 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1745 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1850 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 6, 8, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1386
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 6, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 6, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01468 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  cases hcolor0 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02551 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12096 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0635 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0227 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0228 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0229 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0285 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0227 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0228 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0229 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0285 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0425 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0635 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1797,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00120 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0170 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0170 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06516 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0115 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0115 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0142 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0437 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08304 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0508 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1432 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0508 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1432 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1047 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08577 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0517 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0517 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1441 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1095 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08720 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1446 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0015 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0017 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1446 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1287 chi).mpr
  have hright0 : chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 2, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause09174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0537 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0537 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1461 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0587 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10616 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0585 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1509 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0585 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1509 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1053 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11007 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0598 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1522 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0598 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1522 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0781 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0613 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1537 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0613 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1537 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0789 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11935 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0629 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1553 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0629 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1553 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0837 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12862 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0660 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1584 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0660 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1584 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1577 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0690 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1614 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0690 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1614 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1809 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15269 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0740 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1664 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0740 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1664 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1302 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17010 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0798 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1722 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0798 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1722 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0370 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18778 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0857 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1781 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0857 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1781 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0460 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20009 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0898 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1822 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0898 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1822 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1476 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21711 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0955 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1879 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0955 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1879 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1888 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21770 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1881 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1881 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1984 chi).mpr
  have hright0 : chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨7, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨7, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨7, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
