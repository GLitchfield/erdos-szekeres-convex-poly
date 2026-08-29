module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticSupport

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Common alternate-depth-two clauses, segment 188. -/

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08532 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0516 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0978 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0516 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0978 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0583 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11982 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0631 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1093 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0631 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1093 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1605 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1180 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0718 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1180 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0334 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14827 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1188 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0726 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0726 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1188 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18671 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0854 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0854 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1316 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask0812 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20537 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0916 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1378 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_cupSet_iff_mask1368 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1381 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0919 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0919 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1381 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22242 (chi : TripleColoring 11)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0481 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0482 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0483 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0484 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0485 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0486 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0487 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0488 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0489 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0490 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0491 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0492 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0493 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0494 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0495 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0481 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0482 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0483 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0484 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0485 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0486 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0487 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0488 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0489 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0490 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0491 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0492 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0493 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0494 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0495 at hbad
  rcases hbad with ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14⟩
  have hfive0 : IsStrongPolygonSet chi {6, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1984 chi).mpr
    exact ⟨hq10, hq11, hq12, hq13, hq14⟩
  have hfive1 : IsStrongPolygonSet chi {5, 7, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1952 chi).mpr
    exact ⟨hq6, hq7, hq8, hq9, hq14⟩
  have hfive2 : IsStrongPolygonSet chi {5, 6, 8, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1888 chi).mpr
    exact ⟨hq3, hq4, hq5, hq9, hq13⟩
  have hfive3 : IsStrongPolygonSet chi {5, 6, 7, 9, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1760 chi).mpr
    exact ⟨hq1, hq2, hq5, hq8, hq12⟩
  have hfive4 : IsStrongPolygonSet chi {5, 6, 7, 8, 10} := by
    apply (fin11AltDepth2_strongSet_iff_mask1504 chi).mpr
    exact ⟨hq0, hq2, hq4, hq7, hq11⟩
  have hfive5 : IsStrongPolygonSet chi {5, 6, 7, 8, 9} := by
    apply (fin11AltDepth2_strongSet_iff_mask0992 chi).mpr
    exact ⟨hq0, hq1, hq3, hq6, hq10⟩
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  intro i j k l hij hjk hkl hi hj hk hl
  let t : Finset (Fin 11) := {i, j, k, l}
  have htcard : t.card = 4 := by
    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,
      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),
      ne_of_lt (hij.trans (hjk.trans hkl))]
  have hcardlt : t.card < ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).card := by
    rw [htcard]
    decide
  obtain ⟨x, hxs, hxt⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hmem (y : Fin 11) (hyt : y ∈ t)
      (hy : y ∈ ({5, 6, 7, 8, 9, 10} : Finset (Fin 11))) :
      y ∈ ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase x := by
    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 5 =
          {6, 7, 8, 9, 10} := by decide
    exact hfive0 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 6 =
          {5, 7, 8, 9, 10} := by decide
    exact hfive1 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 7 =
          {5, 6, 8, 9, 10} := by decide
    exact hfive2 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 8 =
          {5, 6, 7, 9, 10} := by decide
    exact hfive3 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 9 =
          {5, 6, 7, 8, 10} := by decide
    exact hfive4 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)
  · have herase :
        ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)).erase 10 =
          {5, 6, 7, 8, 9} := by decide
    exact hfive5 hij hjk hkl
      (herase ▸ hmem i (by simp [t]) hi)
      (herase ▸ hmem j (by simp [t]) hj)
      (herase ▸ hmem k (by simp [t]) hk)
      (herase ▸ hmem l (by simp [t]) hl)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause22695 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0030 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0134 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0974 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0975 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0985 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1213 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0025 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0030 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0134 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0974 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0975 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom0985 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1031 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1087 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1213 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 2, 5, 9, 10}, 4, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1575
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 2, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 2, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 2, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23051 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0995 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0996 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1031 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1122 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1248 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom0995 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom0996 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1006 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1031 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1122 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1248 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 5, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1579
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 5, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23391 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0080 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0155 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1282 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0080 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0155 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1023 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1024 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1029 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1035 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1156 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1282 at h20
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 5, 6, 8, 9}, 10, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0867
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 5, 8, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 1, 6, 8, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 8, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {1, 5, 6, 8, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24243 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0055 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0058 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0061 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0064 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0068 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1100 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1107 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1137 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1368 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0006 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0055 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0058 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0061 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0068 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0076 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1099 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1100 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1107 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1117 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1137 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1368 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 3, 4, 5, 7, 8}, 1, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0441
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 5, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 4, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 3, 5, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {3, 4, 5, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause24579 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0037 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0147 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1133 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1136 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1139 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1155 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1401 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0037 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0147 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1133 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1136 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1139 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1145 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1155 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1401 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 4, 5, 6, 7, 10}, 8, by decide, by decide, Or.inl ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1265
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 5, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 4, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {0, 5, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCupSet chi {4, 5, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26711 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0113 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0122 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0137 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0140 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0144 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1375 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1376 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1379 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1382 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1396 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1411 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0113 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0122 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0137 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0140 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0144 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0156 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0160 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0165 at h14
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
  refine ⟨{3, 4, 6, 7, 9, 10}, 8, by decide, by decide, Or.inl ?_⟩
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23060 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1494 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1585 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1711 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0077 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0128 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1459 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1460 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1463 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1494 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1585 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1711 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 3, 6, 7, 8}, 9, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0459
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 6, 8}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 3, 7, 8}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 6, 7, 8}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 7, 8}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 6, 7, 8}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23174 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0001 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0012 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1469 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1472 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1486 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1597 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1723 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0001 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0012 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0052 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0093 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1469 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1472 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1476 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1486 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1597 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1723 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 1, 4, 5, 6, 9}, 2, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask0627
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 6}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 5, 9}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 4, 6, 9}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 1, 5, 6, 9}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 4, 5, 6, 9}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 4, 5, 6, 9}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause23810 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0036 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0041 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0042 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0100 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0121 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0126 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0157 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1517 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1518 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1524 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1555 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1590 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1786 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0014 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0021 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0036 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0041 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0042 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0085 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0100 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0121 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0126 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0157 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0158 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0164 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1517 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1518 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1524 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1555 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1590 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1786 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{0, 2, 3, 6, 9, 10}, 7, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1613
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 3, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 2, 6, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {0, 3, 6, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 6, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25606 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0092 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1715 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1735 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1840 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0082 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0086 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0088 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0092 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0094 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0101 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at h14
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
  refine ⟨{1, 3, 4, 6, 8, 10}, 2, by decide, by decide, Or.inr ?_⟩
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause25754 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0044 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1710 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1720 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1750 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1855 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0002 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0009 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0022 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0044 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1708 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1709 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1710 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1720 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1750 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1855 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{1, 3, 5, 8, 9, 10}, 0, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1834
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 9}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 8, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 5, 9, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 3, 8, 9, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {1, 5, 8, 9, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 5, 8, 9, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26146 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0047 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1761 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1764 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1783 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1803 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1838 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0046 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0047 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0049 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0050 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0053 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0054 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0057 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0066 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0078 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1761 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1764 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1767 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1783 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1803 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1838 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 6, 7, 10}, 1, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1244
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 7}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 6, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 7, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 6, 7, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 6, 7, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 6, 7, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause26198 (chi : TripleColoring 11)
    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0089 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0096 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0118 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0120 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0133 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1765 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1767 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1769 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1788 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1808 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1843 chi) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at h0
  unfold SynchronizedFiveFanFin11OriginalAtom0089 at h1
  unfold SynchronizedFiveFanFin11OriginalAtom0096 at h2
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at h3
  unfold SynchronizedFiveFanFin11OriginalAtom0099 at h4
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at h5
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at h6
  unfold SynchronizedFiveFanFin11OriginalAtom0118 at h7
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at h8
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at h9
  unfold SynchronizedFiveFanFin11OriginalAtom0133 at h10
  unfold SynchronizedFiveFanFin11OriginalAtom0135 at h11
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at h12
  unfold SynchronizedFiveFanFin11OriginalAtom0152 at h13
  unfold SynchronizedFiveFanFin11OriginalAtom0154 at h14
  unfold SynchronizedFiveFanFin11OriginalAtom1765 at h15
  unfold SynchronizedFiveFanFin11OriginalAtom1767 at h16
  unfold SynchronizedFiveFanFin11OriginalAtom1769 at h17
  unfold SynchronizedFiveFanFin11OriginalAtom1788 at h18
  unfold SynchronizedFiveFanFin11OriginalAtom1808 at h19
  unfold SynchronizedFiveFanFin11OriginalAtom1843 at h20
  have right_of_not_left (t : OrderedTriple 11)
      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by
    cases hcolor : chi t
    · exact (ht hcolor).elim
    · rfl
  apply hno
  unfold SynchronizedFiveFanFin11Conclusion
  refine ⟨{2, 3, 4, 7, 8, 10}, 5, by decide, by decide, Or.inr ?_⟩
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
    have heq := fin11AltDepth2_fiveSubset_mask1436
      polygon hsub hcard
    rcases heq with heq | heq | heq | heq | heq | heq
    · subst polygon
      show IsCapSet chi {2, 3, 4, 7, 8}
      by_contra hnotPure
      apply h15
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 7, 10}
      by_contra hnotPure
      apply h16
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 4, 8, 10}
      by_contra hnotPure
      apply h17
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 3, 7, 8, 10}
      by_contra hnotPure
      apply h18
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {2, 4, 7, 8, 10}
      by_contra hnotPure
      apply h19
      exact ⟨hstrong, hnotPure⟩
    · subst polygon
      show IsCapSet chi {3, 4, 7, 8, 10}
      by_contra hnotPure
      apply h20
      exact ⟨hstrong, hnotPure⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00438 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0007 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0064 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0003 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0007 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0064 at hbad
  cases hcolor0 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00991 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0016 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0087 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0016 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01058 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0011 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0090 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 2) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0011 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0013 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0026 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0090 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01777 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0120 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0035 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0120 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02333 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0028 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0043 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0143 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0028 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0029 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0043 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0143 at hbad
  cases hcolor0 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04036 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0059 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0059 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0081 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04182 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0063 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0136 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0063 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0072 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0136 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04496 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0067 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0149 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0067 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0071 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0149 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04591 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0153 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04730 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0073 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0073 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0079 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0159 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06147 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0107 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0105 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0107 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0162 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07011 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0125 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0129 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11OriginalAtom0125 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0127 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0129 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause07825 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0158 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause08881 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0528 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0174 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0528 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0539,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10084 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0568 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0274 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0568 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause11311 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0609 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0210 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0609 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1109,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12333 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0643 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0243 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0643 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0601,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12996 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0665 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0242 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0244 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0249 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0280 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0242 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0244 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0249 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0280 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0455 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0665 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1353,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13503 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0682 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0261 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0682 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause14673 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0721 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0308 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0721 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0398,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause15872 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0761 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0312 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0761 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause17011 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0335 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0799 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0371 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0838 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause19413 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0879 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0402 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0879 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause20491 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0432 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0432 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0915 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause21664 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0954 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0489 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0954 at hbad
  simp only [
    fin11AltDepth2_strongSet_iff_mask1760,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00593 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0070 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0004 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0070 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0190 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause00696 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0005 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0008 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0005 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0008 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0194 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01761 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0019 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0034 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0239 at hbad
  cases hcolor0 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause01888 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0244 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02508 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0033 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0040 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0032 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0033 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0040 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0150 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0270 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause02781 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0281 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0281 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03256 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0048 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0051 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0069 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0097 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0048 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0051 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0069 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0097 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause03897 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11OriginalAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0056 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0060 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0075 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause04245 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0062 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0062 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0065 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0074 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0138 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0342 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause05592 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0090 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0093 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0398 chi) := by
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

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06144 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0103 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0109 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0103 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0109 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06185 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0104 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0106 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0163 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0104 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0106 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0108 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0163 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause06281 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0132 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0110 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0112 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0117 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0132 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0427 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin11AltDepth2StrongQuad]

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause10791 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0591 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1515 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0010 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0591 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1515 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask0205 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause12529 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1573 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0649 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0649 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1573 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13040 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1590 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0020 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0023 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0024 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0038 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0039 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0045 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0124 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0161 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1590 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask1609 chi).mpr
  have hright0 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause13649 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0686 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1610 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0145 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0686 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1610 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1617 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18229 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1763 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0839 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0839 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1763 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18530 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom1773 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0083 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0084 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0087 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0095 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0098 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0102 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0116 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0119 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0123 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0148 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1773 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (fin11AltDepth2_capSet_iff_mask0620 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11AltDepth2Semantic_clause18749 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11OriginalAtom0856 chi ∧
      SynchronizedFiveFanFin11OriginalAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11OriginalAtom1780 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0130 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom0856 at hbad
  unfold SynchronizedFiveFanFin11OriginalAtom1780 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (fin11AltDepth2_capSet_iff_mask1580 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

end ErdosSzekeres

end
