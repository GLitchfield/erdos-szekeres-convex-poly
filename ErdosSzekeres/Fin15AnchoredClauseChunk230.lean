module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 230. -/

theorem fin15Anchored_clause29440 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2889 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2971 Fin15AnchoredAtom3256 Fin15AnchoredAtom3751 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29441 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2891 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2973 Fin15AnchoredAtom3258 Fin15AnchoredAtom3753 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29442 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2892 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2974 Fin15AnchoredAtom3259 Fin15AnchoredAtom3754 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29443 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2888 Fin15AnchoredAtom2893 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2975 Fin15AnchoredAtom3260 Fin15AnchoredAtom3755 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29444 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2890 chi ∧
      Fin15AnchoredAtom2912 chi ∧
      Fin15AnchoredAtom2976 chi ∧
      Fin15AnchoredAtom3261 chi ∧
      Fin15AnchoredAtom3756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2889 Fin15AnchoredAtom2890 Fin15AnchoredAtom2912
    Fin15AnchoredAtom2976 Fin15AnchoredAtom3261 Fin15AnchoredAtom3756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 11}, {1, 4, 6, 10, 11}, {1, 2, 6, 10, 11}, {1, 2, 4, 10, 11}, {1, 2, 4, 6, 11}, {1, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29445 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2889 Fin15AnchoredAtom2891 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3262 Fin15AnchoredAtom3757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29446 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2889 Fin15AnchoredAtom2892 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3263 Fin15AnchoredAtom3758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29447 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2889 Fin15AnchoredAtom2893 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3264 Fin15AnchoredAtom3759 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29448 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2891 Fin15AnchoredAtom2892 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3268 Fin15AnchoredAtom3763 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29449 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2891 Fin15AnchoredAtom2893 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3269 Fin15AnchoredAtom3764 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29450 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2892 Fin15AnchoredAtom2893 Fin15AnchoredAtom2921
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3270 Fin15AnchoredAtom3765 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29451 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2896 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3277 Fin15AnchoredAtom3772 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 2, 7, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29452 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2898 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3279 Fin15AnchoredAtom3774 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 2, 7, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29453 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2899 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3280 Fin15AnchoredAtom3775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 2, 7, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29454 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2895 Fin15AnchoredAtom2900 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3281 Fin15AnchoredAtom3776 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 2, 7, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29455 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2896 Fin15AnchoredAtom2898 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3283 Fin15AnchoredAtom3778 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29456 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2896 Fin15AnchoredAtom2899 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3284 Fin15AnchoredAtom3779 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29457 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2896 Fin15AnchoredAtom2900 Fin15AnchoredAtom2915
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3285 Fin15AnchoredAtom3780 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29458 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2898 Fin15AnchoredAtom2899 Fin15AnchoredAtom2919
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3289 Fin15AnchoredAtom3784 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29459 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2898 Fin15AnchoredAtom2900 Fin15AnchoredAtom2920
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3290 Fin15AnchoredAtom3785 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29460 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3786 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2899 Fin15AnchoredAtom2900 Fin15AnchoredAtom2921
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3291 Fin15AnchoredAtom3786 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29461 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2907 Fin15AnchoredAtom2909 Fin15AnchoredAtom2913
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3308 Fin15AnchoredAtom3803 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 2, 9, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29462 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2907 Fin15AnchoredAtom2910 Fin15AnchoredAtom2914
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3309 Fin15AnchoredAtom3804 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 2, 9, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29463 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2907 Fin15AnchoredAtom2911 Fin15AnchoredAtom2915
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3310 Fin15AnchoredAtom3805 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 2, 9, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29464 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2909 Fin15AnchoredAtom2910 Fin15AnchoredAtom2919
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3314 Fin15AnchoredAtom3809 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29465 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2909 Fin15AnchoredAtom2911 Fin15AnchoredAtom2920
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3315 Fin15AnchoredAtom3810 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29466 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2910 Fin15AnchoredAtom2911 Fin15AnchoredAtom2921
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3316 Fin15AnchoredAtom3811 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29467 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2913 Fin15AnchoredAtom2914 Fin15AnchoredAtom2919
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3320 Fin15AnchoredAtom3815 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29468 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2913 Fin15AnchoredAtom2915 Fin15AnchoredAtom2920
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3321 Fin15AnchoredAtom3816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29469 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2914 Fin15AnchoredAtom2915 Fin15AnchoredAtom2921
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3322 Fin15AnchoredAtom3817 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29470 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2916 chi ∧
      Fin15AnchoredAtom2917 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3038 chi ∧
      Fin15AnchoredAtom3323 chi ∧
      Fin15AnchoredAtom3818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2916 Fin15AnchoredAtom2917 Fin15AnchoredAtom2919
    Fin15AnchoredAtom3038 Fin15AnchoredAtom3323 Fin15AnchoredAtom3818 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 11, 12, 13}, {1, 4, 11, 12, 13}, {1, 2, 11, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 11, 13}, {1, 2, 4, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29471 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2919 Fin15AnchoredAtom2920 Fin15AnchoredAtom2921
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3326 Fin15AnchoredAtom3821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29472 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2924 Fin15AnchoredAtom2931
    Fin15AnchoredAtom2959 Fin15AnchoredAtom3328 Fin15AnchoredAtom3823 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 9}, {1, 5, 6, 7, 9}, {1, 2, 6, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29473 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2925 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2960 Fin15AnchoredAtom3329 Fin15AnchoredAtom3824 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 10}, {1, 5, 6, 7, 10}, {1, 2, 6, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29474 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2927 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2962 Fin15AnchoredAtom3331 Fin15AnchoredAtom3826 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 12}, {1, 5, 6, 7, 12}, {1, 2, 6, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29475 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2928 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2963 Fin15AnchoredAtom3332 Fin15AnchoredAtom3827 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 13}, {1, 5, 6, 7, 13}, {1, 2, 6, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29476 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2922 Fin15AnchoredAtom2929 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2964 Fin15AnchoredAtom3333 Fin15AnchoredAtom3828 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 14}, {1, 5, 6, 7, 14}, {1, 2, 6, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29477 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2923 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2938 chi ∧
      Fin15AnchoredAtom2966 chi ∧
      Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom3830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2923 Fin15AnchoredAtom2925 Fin15AnchoredAtom2938
    Fin15AnchoredAtom2966 Fin15AnchoredAtom3335 Fin15AnchoredAtom3830 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 8, 10}, {1, 5, 6, 8, 10}, {1, 2, 6, 8, 10}, {1, 2, 5, 8, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29478 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2925 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2971 Fin15AnchoredAtom3340 Fin15AnchoredAtom3835 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 10}, {1, 5, 6, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29479 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2927 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2973 Fin15AnchoredAtom3342 Fin15AnchoredAtom3837 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 12}, {1, 5, 6, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29480 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2928 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2974 Fin15AnchoredAtom3343 Fin15AnchoredAtom3838 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 13}, {1, 5, 6, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29481 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2924 Fin15AnchoredAtom2929 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2975 Fin15AnchoredAtom3344 Fin15AnchoredAtom3839 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 14}, {1, 5, 6, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29482 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2925 Fin15AnchoredAtom2927 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3346 Fin15AnchoredAtom3841 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 12}, {1, 5, 6, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29483 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2925 Fin15AnchoredAtom2928 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3347 Fin15AnchoredAtom3842 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 13}, {1, 5, 6, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29484 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2925 Fin15AnchoredAtom2929 Fin15AnchoredAtom2951
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3348 Fin15AnchoredAtom3843 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 14}, {1, 5, 6, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29485 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2927 Fin15AnchoredAtom2928 Fin15AnchoredAtom2955
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3352 Fin15AnchoredAtom3847 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 12, 13}, {1, 5, 6, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29486 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2927 Fin15AnchoredAtom2929 Fin15AnchoredAtom2956
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3353 Fin15AnchoredAtom3848 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 12, 14}, {1, 5, 6, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29487 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2928 Fin15AnchoredAtom2929 Fin15AnchoredAtom2957
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3354 Fin15AnchoredAtom3849 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 13, 14}, {1, 5, 6, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29488 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2932 Fin15AnchoredAtom2943
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3361 Fin15AnchoredAtom3856 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 2, 7, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29489 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3858 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2934 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3363 Fin15AnchoredAtom3858 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 2, 7, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29490 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2935 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3364 Fin15AnchoredAtom3859 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 2, 7, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29491 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2931 Fin15AnchoredAtom2936 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3365 Fin15AnchoredAtom3860 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 2, 7, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29492 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2932 Fin15AnchoredAtom2934 Fin15AnchoredAtom2949
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3367 Fin15AnchoredAtom3862 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29493 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2932 Fin15AnchoredAtom2935 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3368 Fin15AnchoredAtom3863 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29494 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2932 Fin15AnchoredAtom2936 Fin15AnchoredAtom2951
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3369 Fin15AnchoredAtom3864 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29495 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2934 Fin15AnchoredAtom2935 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3373 Fin15AnchoredAtom3868 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29496 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3869 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2934 Fin15AnchoredAtom2936 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3374 Fin15AnchoredAtom3869 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29497 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2935 Fin15AnchoredAtom2936 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3375 Fin15AnchoredAtom3870 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29498 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2943 Fin15AnchoredAtom2945 Fin15AnchoredAtom2949
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3392 Fin15AnchoredAtom3887 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 2, 9, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29499 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2943 Fin15AnchoredAtom2946 Fin15AnchoredAtom2950
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3393 Fin15AnchoredAtom3888 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 2, 9, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29500 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2943 Fin15AnchoredAtom2947 Fin15AnchoredAtom2951
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3394 Fin15AnchoredAtom3889 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 2, 9, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29501 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2945 Fin15AnchoredAtom2946 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3398 Fin15AnchoredAtom3893 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29502 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2945 Fin15AnchoredAtom2947 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3399 Fin15AnchoredAtom3894 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29503 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2946 Fin15AnchoredAtom2947 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3400 Fin15AnchoredAtom3895 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29504 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2949 Fin15AnchoredAtom2950 Fin15AnchoredAtom2955
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3404 Fin15AnchoredAtom3899 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29505 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2949 Fin15AnchoredAtom2951 Fin15AnchoredAtom2956
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3405 Fin15AnchoredAtom3900 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29506 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2950 Fin15AnchoredAtom2951 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3406 Fin15AnchoredAtom3901 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29507 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2955 Fin15AnchoredAtom2956 Fin15AnchoredAtom2957
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3410 Fin15AnchoredAtom3905 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29508 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2960 Fin15AnchoredAtom2971
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3417 Fin15AnchoredAtom3912 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 10}, {1, 6, 7, 9, 10}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29509 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2962 Fin15AnchoredAtom2973
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3419 Fin15AnchoredAtom3914 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 12}, {1, 6, 7, 9, 12}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29510 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2963 Fin15AnchoredAtom2974
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3420 Fin15AnchoredAtom3915 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 13}, {1, 6, 7, 9, 13}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29511 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2959 Fin15AnchoredAtom2964 Fin15AnchoredAtom2975
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3421 Fin15AnchoredAtom3916 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 14}, {1, 6, 7, 9, 14}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29512 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2960 Fin15AnchoredAtom2962 Fin15AnchoredAtom2977
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3423 Fin15AnchoredAtom3918 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 12}, {1, 6, 7, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29513 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2960 Fin15AnchoredAtom2963 Fin15AnchoredAtom2978
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3424 Fin15AnchoredAtom3919 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 13}, {1, 6, 7, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29514 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2960 Fin15AnchoredAtom2964 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3425 Fin15AnchoredAtom3920 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 14}, {1, 6, 7, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29515 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2962 Fin15AnchoredAtom2963 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3429 Fin15AnchoredAtom3924 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 12, 13}, {1, 6, 7, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29516 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2962 Fin15AnchoredAtom2964 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3430 Fin15AnchoredAtom3925 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 12, 14}, {1, 6, 7, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29517 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2963 Fin15AnchoredAtom2964 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3431 Fin15AnchoredAtom3926 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 13, 14}, {1, 6, 7, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29518 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2971 Fin15AnchoredAtom2973 Fin15AnchoredAtom2977
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3448 Fin15AnchoredAtom3943 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 2, 9, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29519 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2971 Fin15AnchoredAtom2974 Fin15AnchoredAtom2978
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3449 Fin15AnchoredAtom3944 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29520 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2971 Fin15AnchoredAtom2975 Fin15AnchoredAtom2979
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3450 Fin15AnchoredAtom3945 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 2, 9, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29521 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2972 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2980 chi ∧
      Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom3946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2972 Fin15AnchoredAtom2973 Fin15AnchoredAtom2980
    Fin15AnchoredAtom3026 Fin15AnchoredAtom3451 Fin15AnchoredAtom3946 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 11, 12}, {1, 6, 9, 11, 12}, {1, 2, 9, 11, 12}, {1, 2, 6, 11, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29522 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2973 Fin15AnchoredAtom2974 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3454 Fin15AnchoredAtom3949 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29523 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2973 Fin15AnchoredAtom2975 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3455 Fin15AnchoredAtom3950 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29524 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2974 Fin15AnchoredAtom2975 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3456 Fin15AnchoredAtom3951 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29525 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2977 Fin15AnchoredAtom2978 Fin15AnchoredAtom2983
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3460 Fin15AnchoredAtom3955 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29526 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2977 Fin15AnchoredAtom2979 Fin15AnchoredAtom2984
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3461 Fin15AnchoredAtom3956 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29527 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2978 Fin15AnchoredAtom2979 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3462 Fin15AnchoredAtom3957 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29528 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2983 Fin15AnchoredAtom2984 Fin15AnchoredAtom2985
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3466 Fin15AnchoredAtom3961 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29529 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2992 Fin15AnchoredAtom2994 Fin15AnchoredAtom2998
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3483 Fin15AnchoredAtom3978 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 12}, {1, 7, 9, 10, 12}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29530 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2992 Fin15AnchoredAtom2995 Fin15AnchoredAtom2999
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3484 Fin15AnchoredAtom3979 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29531 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2992 Fin15AnchoredAtom2996 Fin15AnchoredAtom3000
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3485 Fin15AnchoredAtom3980 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29532 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2994 Fin15AnchoredAtom2995 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3489 Fin15AnchoredAtom3984 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 12, 13}, {1, 7, 9, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29533 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2994 Fin15AnchoredAtom2996 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3490 Fin15AnchoredAtom3985 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 12, 14}, {1, 7, 9, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29534 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2995 Fin15AnchoredAtom2996 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3491 Fin15AnchoredAtom3986 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 13, 14}, {1, 7, 9, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29535 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2998 Fin15AnchoredAtom2999 Fin15AnchoredAtom3004
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3495 Fin15AnchoredAtom3990 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29536 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2998 Fin15AnchoredAtom3000 Fin15AnchoredAtom3005
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3496 Fin15AnchoredAtom3991 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29537 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2999 Fin15AnchoredAtom3000 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3497 Fin15AnchoredAtom3992 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29538 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3004 Fin15AnchoredAtom3005 Fin15AnchoredAtom3006
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3501 Fin15AnchoredAtom3996 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29539 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3022 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom3032 chi ∧
      Fin15AnchoredAtom3522 chi ∧
      Fin15AnchoredAtom4017 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3022 Fin15AnchoredAtom3023 Fin15AnchoredAtom3026
    Fin15AnchoredAtom3032 Fin15AnchoredAtom3522 Fin15AnchoredAtom4017 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 11, 12}, {1, 9, 10, 11, 12}, {1, 2, 10, 11, 12}, {1, 2, 9, 11, 12}, {1, 2, 9, 10, 12}, {1, 2, 9, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29540 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3023 Fin15AnchoredAtom3024 Fin15AnchoredAtom3029
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3525 Fin15AnchoredAtom4020 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29541 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3023 Fin15AnchoredAtom3025 Fin15AnchoredAtom3030
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3526 Fin15AnchoredAtom4021 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29542 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3024 Fin15AnchoredAtom3025 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3527 Fin15AnchoredAtom4022 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29543 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3029 Fin15AnchoredAtom3030 Fin15AnchoredAtom3031
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3531 Fin15AnchoredAtom4026 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29544 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3035 Fin15AnchoredAtom3036 Fin15AnchoredAtom3037
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3535 Fin15AnchoredAtom4030 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29545 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom4032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3043 Fin15AnchoredAtom3051
    Fin15AnchoredAtom3087 Fin15AnchoredAtom3207 Fin15AnchoredAtom4032 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 7}, {1, 4, 5, 6, 7}, {1, 3, 5, 6, 7}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29546 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom4033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3044 Fin15AnchoredAtom3052
    Fin15AnchoredAtom3088 Fin15AnchoredAtom3208 Fin15AnchoredAtom4033 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 8}, {1, 4, 5, 6, 8}, {1, 3, 5, 6, 8}, {1, 3, 4, 6, 8}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29547 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom4034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3045 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3089 Fin15AnchoredAtom3209 Fin15AnchoredAtom4034 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 9}, {1, 4, 5, 6, 9}, {1, 3, 5, 6, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29548 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom4035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3046 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3090 Fin15AnchoredAtom3210 Fin15AnchoredAtom4035 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 10}, {1, 4, 5, 6, 10}, {1, 3, 5, 6, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29549 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom4037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3048 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3092 Fin15AnchoredAtom3212 Fin15AnchoredAtom4037 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 12}, {1, 4, 5, 6, 12}, {1, 3, 5, 6, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29550 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom4038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3049 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3093 Fin15AnchoredAtom3213 Fin15AnchoredAtom4038 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 13}, {1, 4, 5, 6, 13}, {1, 3, 5, 6, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29551 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom4039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3042 Fin15AnchoredAtom3050 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3094 Fin15AnchoredAtom3214 Fin15AnchoredAtom4039 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 14}, {1, 4, 5, 6, 14}, {1, 3, 5, 6, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29552 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom4040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3044 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3095 Fin15AnchoredAtom3215 Fin15AnchoredAtom4040 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 8}, {1, 4, 5, 7, 8}, {1, 3, 5, 7, 8}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29553 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom4041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3045 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3216 Fin15AnchoredAtom4041 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 9}, {1, 4, 5, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29554 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom4042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3046 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3217 Fin15AnchoredAtom4042 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 10}, {1, 4, 5, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29555 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom4044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3048 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3219 Fin15AnchoredAtom4044 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 12}, {1, 4, 5, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29556 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom4045 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3049 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3220 Fin15AnchoredAtom4045 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 13}, {1, 4, 5, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29557 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom4046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3043 Fin15AnchoredAtom3050 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3221 Fin15AnchoredAtom4046 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 14}, {1, 4, 5, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29558 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom4048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3046 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3103 Fin15AnchoredAtom3223 Fin15AnchoredAtom4048 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 10}, {1, 4, 5, 8, 10}, {1, 3, 5, 8, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29559 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom4050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3048 Fin15AnchoredAtom3069
    Fin15AnchoredAtom3105 Fin15AnchoredAtom3225 Fin15AnchoredAtom4050 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 12}, {1, 4, 5, 8, 12}, {1, 3, 5, 8, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29560 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom4051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3049 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3106 Fin15AnchoredAtom3226 Fin15AnchoredAtom4051 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 13}, {1, 4, 5, 8, 13}, {1, 3, 5, 8, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29561 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom4052 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3044 Fin15AnchoredAtom3050 Fin15AnchoredAtom3071
    Fin15AnchoredAtom3107 Fin15AnchoredAtom3227 Fin15AnchoredAtom4052 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 14}, {1, 4, 5, 8, 14}, {1, 3, 5, 8, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29562 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom4053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3046 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3228 Fin15AnchoredAtom4053 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 10}, {1, 4, 5, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29563 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom4055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3048 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3230 Fin15AnchoredAtom4055 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 12}, {1, 4, 5, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29564 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom4056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3049 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3231 Fin15AnchoredAtom4056 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 13}, {1, 4, 5, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29565 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom4057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3045 Fin15AnchoredAtom3050 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3232 Fin15AnchoredAtom4057 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 14}, {1, 4, 5, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29566 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom4059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3046 Fin15AnchoredAtom3048 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3234 Fin15AnchoredAtom4059 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 12}, {1, 4, 5, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29567 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom4060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3046 Fin15AnchoredAtom3049 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3235 Fin15AnchoredAtom4060 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 13}, {1, 4, 5, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
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
