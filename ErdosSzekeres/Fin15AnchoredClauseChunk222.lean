module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 222. -/

theorem fin15Anchored_clause28416 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom3112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1900 Fin15AnchoredAtom1905 Fin15AnchoredAtom1931
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2397 Fin15AnchoredAtom3112 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 9, 14}, {0, 3, 5, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28417 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom3114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1933
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2399 Fin15AnchoredAtom3114 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 10, 12}, {0, 3, 5, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28418 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom3115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1901 Fin15AnchoredAtom1904 Fin15AnchoredAtom1934
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2400 Fin15AnchoredAtom3115 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 10, 13}, {0, 3, 5, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28419 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom3116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1901 Fin15AnchoredAtom1905 Fin15AnchoredAtom1935
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2401 Fin15AnchoredAtom3116 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 10, 14}, {0, 3, 5, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28420 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom3120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2405 Fin15AnchoredAtom3120 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 12, 13}, {0, 3, 5, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28421 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom3121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1903 Fin15AnchoredAtom1905 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2406 Fin15AnchoredAtom3121 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 12, 14}, {0, 3, 5, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28422 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom3122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2407 Fin15AnchoredAtom3122 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 5, 13, 14}, {0, 3, 5, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28423 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom3123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1907 Fin15AnchoredAtom1914
    Fin15AnchoredAtom2023 Fin15AnchoredAtom2408 Fin15AnchoredAtom3123 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 8}, {0, 3, 6, 7, 8}, {0, 1, 6, 7, 8}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28424 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom3124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1908 Fin15AnchoredAtom1915
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2409 Fin15AnchoredAtom3124 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 1, 6, 7, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28425 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom3125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1909 Fin15AnchoredAtom1916
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2410 Fin15AnchoredAtom3125 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 1, 6, 7, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28426 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom3127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1911 Fin15AnchoredAtom1918
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2412 Fin15AnchoredAtom3127 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 1, 6, 7, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28427 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom3128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1912 Fin15AnchoredAtom1919
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2413 Fin15AnchoredAtom3128 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 1, 6, 7, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28428 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom3129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1906 Fin15AnchoredAtom1913 Fin15AnchoredAtom1920
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2414 Fin15AnchoredAtom3129 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 1, 6, 7, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28429 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom3130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1908 Fin15AnchoredAtom1921
    Fin15AnchoredAtom2030 Fin15AnchoredAtom2415 Fin15AnchoredAtom3130 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 8, 9}, {0, 3, 6, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28430 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom3131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1909 Fin15AnchoredAtom1922
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2416 Fin15AnchoredAtom3131 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 8, 10}, {0, 3, 6, 8, 10}, {0, 1, 6, 8, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28431 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom3135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1907 Fin15AnchoredAtom1913 Fin15AnchoredAtom1926
    Fin15AnchoredAtom2035 Fin15AnchoredAtom2420 Fin15AnchoredAtom3135 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 8, 14}, {0, 3, 6, 8, 14}, {0, 1, 6, 8, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28432 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom3136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1909 Fin15AnchoredAtom1927
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2421 Fin15AnchoredAtom3136 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28433 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom3138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1911 Fin15AnchoredAtom1929
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2423 Fin15AnchoredAtom3138 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28434 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom3139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1912 Fin15AnchoredAtom1930
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2424 Fin15AnchoredAtom3139 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28435 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom3140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1908 Fin15AnchoredAtom1913 Fin15AnchoredAtom1931
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2425 Fin15AnchoredAtom3140 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28436 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom3142 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1909 Fin15AnchoredAtom1911 Fin15AnchoredAtom1933
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2427 Fin15AnchoredAtom3142 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28437 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom3143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1909 Fin15AnchoredAtom1912 Fin15AnchoredAtom1934
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2428 Fin15AnchoredAtom3143 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28438 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom3144 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1909 Fin15AnchoredAtom1913 Fin15AnchoredAtom1935
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2429 Fin15AnchoredAtom3144 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28439 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom3148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1911 Fin15AnchoredAtom1912 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2433 Fin15AnchoredAtom3148 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28440 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom3149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1911 Fin15AnchoredAtom1913 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2434 Fin15AnchoredAtom3149 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28441 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom3150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1912 Fin15AnchoredAtom1913 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2435 Fin15AnchoredAtom3150 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28442 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom3151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1914 Fin15AnchoredAtom1915 Fin15AnchoredAtom1921
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2436 Fin15AnchoredAtom3151 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 8, 9}, {0, 3, 7, 8, 9}, {0, 1, 7, 8, 9}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28443 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom3152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1914 Fin15AnchoredAtom1916 Fin15AnchoredAtom1922
    Fin15AnchoredAtom2052 Fin15AnchoredAtom2437 Fin15AnchoredAtom3152 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 8, 10}, {0, 3, 7, 8, 10}, {0, 1, 7, 8, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28444 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom3156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1914 Fin15AnchoredAtom1920 Fin15AnchoredAtom1926
    Fin15AnchoredAtom2056 Fin15AnchoredAtom2441 Fin15AnchoredAtom3156 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 8, 14}, {0, 3, 7, 8, 14}, {0, 1, 7, 8, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28445 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom3157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1916 Fin15AnchoredAtom1927
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2442 Fin15AnchoredAtom3157 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28446 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom3159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1918 Fin15AnchoredAtom1929
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2444 Fin15AnchoredAtom3159 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28447 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom3160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1919 Fin15AnchoredAtom1930
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2445 Fin15AnchoredAtom3160 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28448 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom3161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1915 Fin15AnchoredAtom1920 Fin15AnchoredAtom1931
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2446 Fin15AnchoredAtom3161 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28449 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom3163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1916 Fin15AnchoredAtom1918 Fin15AnchoredAtom1933
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2448 Fin15AnchoredAtom3163 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28450 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom3164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1916 Fin15AnchoredAtom1919 Fin15AnchoredAtom1934
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2449 Fin15AnchoredAtom3164 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28451 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom3165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1916 Fin15AnchoredAtom1920 Fin15AnchoredAtom1935
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2450 Fin15AnchoredAtom3165 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28452 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom3169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1918 Fin15AnchoredAtom1919 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2454 Fin15AnchoredAtom3169 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28453 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom3170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1918 Fin15AnchoredAtom1920 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2455 Fin15AnchoredAtom3170 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28454 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom3171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1919 Fin15AnchoredAtom1920 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2456 Fin15AnchoredAtom3171 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28455 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom3172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1921 Fin15AnchoredAtom1922 Fin15AnchoredAtom1927
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2457 Fin15AnchoredAtom3172 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 1, 8, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28456 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom3174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1921 Fin15AnchoredAtom1924 Fin15AnchoredAtom1929
    Fin15AnchoredAtom2074 Fin15AnchoredAtom2459 Fin15AnchoredAtom3174 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 9, 12}, {0, 3, 8, 9, 12}, {0, 1, 8, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28457 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom3175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1921 Fin15AnchoredAtom1925 Fin15AnchoredAtom1930
    Fin15AnchoredAtom2075 Fin15AnchoredAtom2460 Fin15AnchoredAtom3175 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 9, 13}, {0, 3, 8, 9, 13}, {0, 1, 8, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28458 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom3176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1921 Fin15AnchoredAtom1926 Fin15AnchoredAtom1931
    Fin15AnchoredAtom2076 Fin15AnchoredAtom2461 Fin15AnchoredAtom3176 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 9, 14}, {0, 3, 8, 9, 14}, {0, 1, 8, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28459 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom3178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1922 Fin15AnchoredAtom1924 Fin15AnchoredAtom1933
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2463 Fin15AnchoredAtom3178 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 10, 12}, {0, 3, 8, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28460 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom3179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1922 Fin15AnchoredAtom1925 Fin15AnchoredAtom1934
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2464 Fin15AnchoredAtom3179 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 10, 13}, {0, 3, 8, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28461 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom3180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1922 Fin15AnchoredAtom1926 Fin15AnchoredAtom1935
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2465 Fin15AnchoredAtom3180 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 10, 14}, {0, 3, 8, 10, 14}, {0, 1, 8, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28462 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom3184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1924 Fin15AnchoredAtom1925 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2084 Fin15AnchoredAtom2469 Fin15AnchoredAtom3184 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 12, 13}, {0, 3, 8, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28463 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom3185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1924 Fin15AnchoredAtom1926 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2470 Fin15AnchoredAtom3185 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 12, 14}, {0, 3, 8, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28464 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom3186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1925 Fin15AnchoredAtom1926 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2471 Fin15AnchoredAtom3186 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 8, 13, 14}, {0, 3, 8, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28465 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom3188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1927 Fin15AnchoredAtom1929 Fin15AnchoredAtom1933
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2473 Fin15AnchoredAtom3188 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28466 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom3189 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1927 Fin15AnchoredAtom1930 Fin15AnchoredAtom1934
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2474 Fin15AnchoredAtom3189 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28467 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom3190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1927 Fin15AnchoredAtom1931 Fin15AnchoredAtom1935
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2475 Fin15AnchoredAtom3190 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28468 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1928 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom2092 chi ∧
      Fin15AnchoredAtom2477 chi ∧
      Fin15AnchoredAtom3192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1928 Fin15AnchoredAtom1930 Fin15AnchoredAtom1937
    Fin15AnchoredAtom2092 Fin15AnchoredAtom2477 Fin15AnchoredAtom3192 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 11, 13}, {0, 3, 9, 11, 13}, {0, 1, 9, 11, 13}, {0, 1, 3, 11, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28469 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom3194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1929 Fin15AnchoredAtom1930 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2479 Fin15AnchoredAtom3194 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28470 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom3195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1929 Fin15AnchoredAtom1931 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2480 Fin15AnchoredAtom3195 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28471 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom3196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1930 Fin15AnchoredAtom1931 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2481 Fin15AnchoredAtom3196 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28472 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom3200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1933 Fin15AnchoredAtom1934 Fin15AnchoredAtom1939
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2485 Fin15AnchoredAtom3200 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28473 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom3201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1933 Fin15AnchoredAtom1935 Fin15AnchoredAtom1940
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2486 Fin15AnchoredAtom3201 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28474 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom3202 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1934 Fin15AnchoredAtom1935 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2487 Fin15AnchoredAtom3202 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28475 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom3206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1939 Fin15AnchoredAtom1940 Fin15AnchoredAtom1941
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2491 Fin15AnchoredAtom3206 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 3, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 3, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28476 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom3207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1987 Fin15AnchoredAtom2492 Fin15AnchoredAtom3207 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 7}, {0, 4, 5, 6, 7}, {0, 1, 5, 6, 7}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28477 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom3209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1989 Fin15AnchoredAtom2494 Fin15AnchoredAtom3209 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 9}, {0, 4, 5, 6, 9}, {0, 1, 5, 6, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28478 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom3210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1946 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1990 Fin15AnchoredAtom2495 Fin15AnchoredAtom3210 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 10}, {0, 4, 5, 6, 10}, {0, 1, 5, 6, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28479 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom3212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1948 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1992 Fin15AnchoredAtom2497 Fin15AnchoredAtom3212 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 12}, {0, 4, 5, 6, 12}, {0, 1, 5, 6, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28480 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom3213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1949 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2498 Fin15AnchoredAtom3213 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 13}, {0, 4, 5, 6, 13}, {0, 1, 5, 6, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28481 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom3214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1942 Fin15AnchoredAtom1950 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2499 Fin15AnchoredAtom3214 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 6, 14}, {0, 4, 5, 6, 14}, {0, 1, 5, 6, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28482 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom3216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2501 Fin15AnchoredAtom3216 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 7, 9}, {0, 4, 5, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28483 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom3217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2502 Fin15AnchoredAtom3217 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 7, 10}, {0, 4, 5, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28484 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom3219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1948 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2504 Fin15AnchoredAtom3219 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 7, 12}, {0, 4, 5, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28485 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom3220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1949 Fin15AnchoredAtom1964
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2505 Fin15AnchoredAtom3220 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 7, 13}, {0, 4, 5, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28486 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom3221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1943 Fin15AnchoredAtom1950 Fin15AnchoredAtom1965
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2506 Fin15AnchoredAtom3221 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 7, 14}, {0, 4, 5, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28487 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom3228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2513 Fin15AnchoredAtom3228 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 9, 10}, {0, 4, 5, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28488 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom3230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2515 Fin15AnchoredAtom3230 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 9, 12}, {0, 4, 5, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28489 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom3231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2516 Fin15AnchoredAtom3231 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 9, 13}, {0, 4, 5, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28490 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom3232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2517 Fin15AnchoredAtom3232 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 9, 14}, {0, 4, 5, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28491 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom3234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2519 Fin15AnchoredAtom3234 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 10, 12}, {0, 4, 5, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28492 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom3235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2520 Fin15AnchoredAtom3235 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 10, 13}, {0, 4, 5, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28493 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom3236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2521 Fin15AnchoredAtom3236 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 10, 14}, {0, 4, 5, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28494 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom3240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2525 Fin15AnchoredAtom3240 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 12, 13}, {0, 4, 5, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28495 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom3241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2526 Fin15AnchoredAtom3241 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 12, 14}, {0, 4, 5, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28496 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom3242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2527 Fin15AnchoredAtom3242 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 5, 13, 14}, {0, 4, 5, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28497 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom3244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1960
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2529 Fin15AnchoredAtom3244 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 1, 6, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28498 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom3245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1961
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2530 Fin15AnchoredAtom3245 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 1, 6, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28499 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom3247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1956 Fin15AnchoredAtom1963
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2532 Fin15AnchoredAtom3247 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 1, 6, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28500 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom3248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1957 Fin15AnchoredAtom1964
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2533 Fin15AnchoredAtom3248 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 1, 6, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28501 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom3249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1951 Fin15AnchoredAtom1958 Fin15AnchoredAtom1965
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2534 Fin15AnchoredAtom3249 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 1, 6, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28502 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom3250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1953 Fin15AnchoredAtom1966
    Fin15AnchoredAtom2030 Fin15AnchoredAtom2535 Fin15AnchoredAtom3250 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 8, 9}, {0, 4, 6, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28503 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom3251 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1954 Fin15AnchoredAtom1967
    Fin15AnchoredAtom2031 Fin15AnchoredAtom2536 Fin15AnchoredAtom3251 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 8, 10}, {0, 4, 6, 8, 10}, {0, 1, 6, 8, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28504 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom3253 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1952 Fin15AnchoredAtom1956 Fin15AnchoredAtom1969
    Fin15AnchoredAtom2033 Fin15AnchoredAtom2538 Fin15AnchoredAtom3253 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 8, 12}, {0, 4, 6, 8, 12}, {0, 1, 6, 8, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28505 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom3256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2541 Fin15AnchoredAtom3256 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28506 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom3258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2543 Fin15AnchoredAtom3258 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28507 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom3259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1957 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2544 Fin15AnchoredAtom3259 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28508 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom3260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1953 Fin15AnchoredAtom1958 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2545 Fin15AnchoredAtom3260 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28509 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom3262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2547 Fin15AnchoredAtom3262 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28510 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom3263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2548 Fin15AnchoredAtom3263 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28511 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom3264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2549 Fin15AnchoredAtom3264 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28512 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom3268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2553 Fin15AnchoredAtom3268 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28513 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom3269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2554 Fin15AnchoredAtom3269 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28514 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom3270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2555 Fin15AnchoredAtom3270 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28515 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom3271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1960 Fin15AnchoredAtom1966
    Fin15AnchoredAtom2051 Fin15AnchoredAtom2556 Fin15AnchoredAtom3271 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 1, 7, 8, 9}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28516 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom3275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1959 Fin15AnchoredAtom1964 Fin15AnchoredAtom1970
    Fin15AnchoredAtom2055 Fin15AnchoredAtom2560 Fin15AnchoredAtom3275 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 8, 13}, {0, 4, 7, 8, 13}, {0, 1, 7, 8, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28517 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom3277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2562 Fin15AnchoredAtom3277 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28518 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom3279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2564 Fin15AnchoredAtom3279 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28519 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom3280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2565 Fin15AnchoredAtom3280 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28520 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom3281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1960 Fin15AnchoredAtom1965 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2566 Fin15AnchoredAtom3281 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28521 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom3283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2568 Fin15AnchoredAtom3283 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28522 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom3284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2569 Fin15AnchoredAtom3284 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28523 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom3285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1961 Fin15AnchoredAtom1965 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2570 Fin15AnchoredAtom3285 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28524 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom3289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2574 Fin15AnchoredAtom3289 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28525 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom3290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2575 Fin15AnchoredAtom3290 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28526 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom3291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2576 Fin15AnchoredAtom3291 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28527 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom3292 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1966 Fin15AnchoredAtom1967 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2072 Fin15AnchoredAtom2577 Fin15AnchoredAtom3292 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 1, 8, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28528 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom3298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1967 Fin15AnchoredAtom1969 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2078 Fin15AnchoredAtom2583 Fin15AnchoredAtom3298 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28529 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom3299 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1967 Fin15AnchoredAtom1970 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2079 Fin15AnchoredAtom2584 Fin15AnchoredAtom3299 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28530 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom3300 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1967 Fin15AnchoredAtom1971 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2080 Fin15AnchoredAtom2585 Fin15AnchoredAtom3300 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 10, 14}, {0, 4, 8, 10, 14}, {0, 1, 8, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28531 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom3305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1969 Fin15AnchoredAtom1971 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2085 Fin15AnchoredAtom2590 Fin15AnchoredAtom3305 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28532 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom3306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1970 Fin15AnchoredAtom1971 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2086 Fin15AnchoredAtom2591 Fin15AnchoredAtom3306 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 8, 13, 14}, {0, 4, 8, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28533 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom3308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2593 Fin15AnchoredAtom3308 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 1, 9, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28534 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom3309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2594 Fin15AnchoredAtom3309 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 1, 9, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28535 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom3310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1972 Fin15AnchoredAtom1976 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2595 Fin15AnchoredAtom3310 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 1, 9, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28536 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom3314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2599 Fin15AnchoredAtom3314 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28537 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom3315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2600 Fin15AnchoredAtom3315 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28538 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom3316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2601 Fin15AnchoredAtom3316 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28539 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom3320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2605 Fin15AnchoredAtom3320 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28540 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom3321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2606 Fin15AnchoredAtom3321 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28541 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom3322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2607 Fin15AnchoredAtom3322 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28542 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom3326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2611 Fin15AnchoredAtom3326 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 4, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 1, 12, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28543 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom3328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2613 Fin15AnchoredAtom3328 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 5, 6, 7, 9}, {0, 5, 6, 7, 9}, {0, 1, 6, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

end ErdosSzekeres

end
