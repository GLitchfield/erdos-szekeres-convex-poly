module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 229. -/

theorem fin15Anchored_clause29312 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2759 Fin15AnchoredAtom2760 Fin15AnchoredAtom2766
    Fin15AnchoredAtom2782 Fin15AnchoredAtom2802 Fin15AnchoredAtom4783 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29313 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2764 Fin15AnchoredAtom2765 Fin15AnchoredAtom2766
    Fin15AnchoredAtom2786 Fin15AnchoredAtom2806 Fin15AnchoredAtom4787 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29314 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2767 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2772 chi ∧
      Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom4789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2767 Fin15AnchoredAtom2769 Fin15AnchoredAtom2772
    Fin15AnchoredAtom2778 Fin15AnchoredAtom2808 Fin15AnchoredAtom4789 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 9, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 13}, {0, 9, 10, 11, 13}, {0, 7, 10, 11, 13}, {0, 7, 9, 11, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29315 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2768 Fin15AnchoredAtom2769 Fin15AnchoredAtom2774
    Fin15AnchoredAtom2780 Fin15AnchoredAtom2810 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29316 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2768 Fin15AnchoredAtom2770 Fin15AnchoredAtom2775
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2811 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29317 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2769 Fin15AnchoredAtom2770 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2782 Fin15AnchoredAtom2812 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29318 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2774 Fin15AnchoredAtom2775 Fin15AnchoredAtom2776
    Fin15AnchoredAtom2786 Fin15AnchoredAtom2816 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29319 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom2779 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2784 chi ∧
      Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom4799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2777 Fin15AnchoredAtom2779 Fin15AnchoredAtom2781
    Fin15AnchoredAtom2784 Fin15AnchoredAtom2818 Fin15AnchoredAtom4799 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 10, 11, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 14}, {0, 10, 11, 12, 14}, {0, 7, 11, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29320 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2780 Fin15AnchoredAtom2781 Fin15AnchoredAtom2782
    Fin15AnchoredAtom2786 Fin15AnchoredAtom2820 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29321 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2788 Fin15AnchoredAtom2789 Fin15AnchoredAtom2794
    Fin15AnchoredAtom2800 Fin15AnchoredAtom2810 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29322 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2788 Fin15AnchoredAtom2790 Fin15AnchoredAtom2795
    Fin15AnchoredAtom2801 Fin15AnchoredAtom2811 Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 8, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29323 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2789 Fin15AnchoredAtom2790 Fin15AnchoredAtom2796
    Fin15AnchoredAtom2802 Fin15AnchoredAtom2812 Fin15AnchoredAtom4808 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 8, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29324 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2794 Fin15AnchoredAtom2795 Fin15AnchoredAtom2796
    Fin15AnchoredAtom2806 Fin15AnchoredAtom2816 Fin15AnchoredAtom4812 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 8, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29325 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2800 Fin15AnchoredAtom2801 Fin15AnchoredAtom2802
    Fin15AnchoredAtom2806 Fin15AnchoredAtom2820 Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 8, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29326 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom2814 chi ∧
      Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom4819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2807 Fin15AnchoredAtom2809 Fin15AnchoredAtom2811
    Fin15AnchoredAtom2814 Fin15AnchoredAtom2818 Fin15AnchoredAtom4819 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 9, 10, 11, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 9, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 9, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 14}, {0, 10, 11, 12, 14}, {0, 9, 11, 12, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 11, 14}, {0, 9, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29327 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom2815 chi ∧
      Fin15AnchoredAtom2819 chi ∧
      Fin15AnchoredAtom4820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2808 Fin15AnchoredAtom2809 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2815 Fin15AnchoredAtom2819 Fin15AnchoredAtom4820 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 9, 10, 11, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 9, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 9, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 13, 14}, {0, 10, 11, 13, 14}, {0, 9, 11, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 11, 14}, {0, 9, 10, 11, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29328 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2810 Fin15AnchoredAtom2811 Fin15AnchoredAtom2812
    Fin15AnchoredAtom2816 Fin15AnchoredAtom2820 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29329 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2877 Fin15AnchoredAtom3042 Fin15AnchoredAtom3537 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 6}, {1, 3, 4, 5, 6}, {1, 2, 4, 5, 6}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29330 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2878 Fin15AnchoredAtom3043 Fin15AnchoredAtom3538 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 7}, {1, 3, 4, 5, 7}, {1, 2, 4, 5, 7}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29331 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2880 Fin15AnchoredAtom3045 Fin15AnchoredAtom3540 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 9}, {1, 3, 4, 5, 9}, {1, 2, 4, 5, 9}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29332 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2881 Fin15AnchoredAtom3046 Fin15AnchoredAtom3541 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 10}, {1, 3, 4, 5, 10}, {1, 2, 4, 5, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29333 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2829 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2883 Fin15AnchoredAtom3048 Fin15AnchoredAtom3543 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 12}, {1, 3, 4, 5, 12}, {1, 2, 4, 5, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29334 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2830 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2884 Fin15AnchoredAtom3049 Fin15AnchoredAtom3544 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 13}, {1, 3, 4, 5, 13}, {1, 2, 4, 5, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29335 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2822 Fin15AnchoredAtom2831 Fin15AnchoredAtom2840
    Fin15AnchoredAtom2885 Fin15AnchoredAtom3050 Fin15AnchoredAtom3545 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 5, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 5, 14}, {1, 3, 4, 5, 14}, {1, 2, 4, 5, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29336 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2886 Fin15AnchoredAtom3051 Fin15AnchoredAtom3546 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 7}, {1, 3, 4, 6, 7}, {1, 2, 4, 6, 7}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29337 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2888 Fin15AnchoredAtom3053 Fin15AnchoredAtom3548 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 9}, {1, 3, 4, 6, 9}, {1, 2, 4, 6, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29338 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2889 Fin15AnchoredAtom3054 Fin15AnchoredAtom3549 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 10}, {1, 3, 4, 6, 10}, {1, 2, 4, 6, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29339 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2829 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2891 Fin15AnchoredAtom3056 Fin15AnchoredAtom3551 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 12}, {1, 3, 4, 6, 12}, {1, 2, 4, 6, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29340 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2830 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2892 Fin15AnchoredAtom3057 Fin15AnchoredAtom3552 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 13}, {1, 3, 4, 6, 13}, {1, 2, 4, 6, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29341 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2823 Fin15AnchoredAtom2831 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2893 Fin15AnchoredAtom3058 Fin15AnchoredAtom3553 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 6, 14}, {1, 3, 4, 6, 14}, {1, 2, 4, 6, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29342 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2895 Fin15AnchoredAtom3060 Fin15AnchoredAtom3555 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 9}, {1, 3, 4, 7, 9}, {1, 2, 4, 7, 9}, {1, 2, 3, 7, 9}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29343 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2896 Fin15AnchoredAtom3061 Fin15AnchoredAtom3556 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 10}, {1, 3, 4, 7, 10}, {1, 2, 4, 7, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29344 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2898 Fin15AnchoredAtom3063 Fin15AnchoredAtom3558 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 12}, {1, 3, 4, 7, 12}, {1, 2, 4, 7, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29345 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2830 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2899 Fin15AnchoredAtom3064 Fin15AnchoredAtom3559 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 13}, {1, 3, 4, 7, 13}, {1, 2, 4, 7, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29346 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2824 Fin15AnchoredAtom2831 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2900 Fin15AnchoredAtom3065 Fin15AnchoredAtom3560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 7, 14}, {1, 3, 4, 7, 14}, {1, 2, 4, 7, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29347 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2907 Fin15AnchoredAtom3072 Fin15AnchoredAtom3567 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 10}, {1, 3, 4, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 3, 9, 10}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29348 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2909 Fin15AnchoredAtom3074 Fin15AnchoredAtom3569 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 12}, {1, 3, 4, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29349 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2830 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2910 Fin15AnchoredAtom3075 Fin15AnchoredAtom3570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 13}, {1, 3, 4, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29350 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2826 Fin15AnchoredAtom2831 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2911 Fin15AnchoredAtom3076 Fin15AnchoredAtom3571 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 9, 14}, {1, 3, 4, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29351 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2913 Fin15AnchoredAtom3078 Fin15AnchoredAtom3573 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 12}, {1, 3, 4, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 3, 10, 12}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29352 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2914 Fin15AnchoredAtom3079 Fin15AnchoredAtom3574 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 13}, {1, 3, 4, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29353 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2827 Fin15AnchoredAtom2831 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2915 Fin15AnchoredAtom3080 Fin15AnchoredAtom3575 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 14}, {1, 3, 4, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29354 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2919 Fin15AnchoredAtom3084 Fin15AnchoredAtom3579 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 12, 13}, {1, 3, 4, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29355 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2875
    Fin15AnchoredAtom2920 Fin15AnchoredAtom3085 Fin15AnchoredAtom3580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 12, 14}, {1, 3, 4, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29356 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2876
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3086 Fin15AnchoredAtom3581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 4, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 13, 14}, {1, 3, 4, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29357 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2922 Fin15AnchoredAtom3087 Fin15AnchoredAtom3582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 7}, {1, 3, 5, 6, 7}, {1, 2, 5, 6, 7}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29358 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2924 Fin15AnchoredAtom3089 Fin15AnchoredAtom3584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 9}, {1, 3, 5, 6, 9}, {1, 2, 5, 6, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29359 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2925 Fin15AnchoredAtom3090 Fin15AnchoredAtom3585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 10}, {1, 3, 5, 6, 10}, {1, 2, 5, 6, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29360 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2927 Fin15AnchoredAtom3092 Fin15AnchoredAtom3587 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 12}, {1, 3, 5, 6, 12}, {1, 2, 5, 6, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29361 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2839 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2928 Fin15AnchoredAtom3093 Fin15AnchoredAtom3588 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 13}, {1, 3, 5, 6, 13}, {1, 2, 5, 6, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29362 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2832 Fin15AnchoredAtom2840 Fin15AnchoredAtom2848
    Fin15AnchoredAtom2929 Fin15AnchoredAtom3094 Fin15AnchoredAtom3589 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 14}, {1, 3, 5, 6, 14}, {1, 2, 5, 6, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29363 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2931 Fin15AnchoredAtom3096 Fin15AnchoredAtom3591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 9}, {1, 3, 5, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29364 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2932 Fin15AnchoredAtom3097 Fin15AnchoredAtom3592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 10}, {1, 3, 5, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29365 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2934 Fin15AnchoredAtom3099 Fin15AnchoredAtom3594 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 12}, {1, 3, 5, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29366 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2839 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2935 Fin15AnchoredAtom3100 Fin15AnchoredAtom3595 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 13}, {1, 3, 5, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29367 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2833 Fin15AnchoredAtom2840 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2936 Fin15AnchoredAtom3101 Fin15AnchoredAtom3596 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 14}, {1, 3, 5, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29368 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2943 Fin15AnchoredAtom3108 Fin15AnchoredAtom3603 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 10}, {1, 3, 5, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29369 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2945 Fin15AnchoredAtom3110 Fin15AnchoredAtom3605 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 12}, {1, 3, 5, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29370 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2839 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2946 Fin15AnchoredAtom3111 Fin15AnchoredAtom3606 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 13}, {1, 3, 5, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29371 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2835 Fin15AnchoredAtom2840 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2947 Fin15AnchoredAtom3112 Fin15AnchoredAtom3607 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 14}, {1, 3, 5, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29372 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2949 Fin15AnchoredAtom3114 Fin15AnchoredAtom3609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 12}, {1, 3, 5, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29373 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2950 Fin15AnchoredAtom3115 Fin15AnchoredAtom3610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 13}, {1, 3, 5, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29374 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2836 Fin15AnchoredAtom2840 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3116 Fin15AnchoredAtom3611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 14}, {1, 3, 5, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29375 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3120 Fin15AnchoredAtom3615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 12, 13}, {1, 3, 5, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29376 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2838 Fin15AnchoredAtom2840 Fin15AnchoredAtom2875
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3121 Fin15AnchoredAtom3616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 12, 14}, {1, 3, 5, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29377 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2876
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3122 Fin15AnchoredAtom3617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 13, 14}, {1, 3, 5, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29378 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2843 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2959 Fin15AnchoredAtom3124 Fin15AnchoredAtom3619 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 9}, {1, 3, 6, 7, 9}, {1, 2, 6, 7, 9}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29379 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2844 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2960 Fin15AnchoredAtom3125 Fin15AnchoredAtom3620 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 10}, {1, 3, 6, 7, 10}, {1, 2, 6, 7, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29380 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2846 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2962 Fin15AnchoredAtom3127 Fin15AnchoredAtom3622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 12}, {1, 3, 6, 7, 12}, {1, 2, 6, 7, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29381 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2847 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2963 Fin15AnchoredAtom3128 Fin15AnchoredAtom3623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 13}, {1, 3, 6, 7, 13}, {1, 2, 6, 7, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29382 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2841 Fin15AnchoredAtom2848 Fin15AnchoredAtom2855
    Fin15AnchoredAtom2964 Fin15AnchoredAtom3129 Fin15AnchoredAtom3624 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 14}, {1, 3, 6, 7, 14}, {1, 2, 6, 7, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29383 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2844 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2971 Fin15AnchoredAtom3136 Fin15AnchoredAtom3631 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 10}, {1, 3, 6, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29384 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2846 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2973 Fin15AnchoredAtom3138 Fin15AnchoredAtom3633 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 12}, {1, 3, 6, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29385 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2847 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2974 Fin15AnchoredAtom3139 Fin15AnchoredAtom3634 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 13}, {1, 3, 6, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29386 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2843 Fin15AnchoredAtom2848 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2975 Fin15AnchoredAtom3140 Fin15AnchoredAtom3635 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 14}, {1, 3, 6, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29387 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2844 Fin15AnchoredAtom2846 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2977 Fin15AnchoredAtom3142 Fin15AnchoredAtom3637 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 12}, {1, 3, 6, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29388 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2844 Fin15AnchoredAtom2847 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2978 Fin15AnchoredAtom3143 Fin15AnchoredAtom3638 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 13}, {1, 3, 6, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29389 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2844 Fin15AnchoredAtom2848 Fin15AnchoredAtom2870
    Fin15AnchoredAtom2979 Fin15AnchoredAtom3144 Fin15AnchoredAtom3639 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 14}, {1, 3, 6, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29390 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2846 Fin15AnchoredAtom2847 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2983 Fin15AnchoredAtom3148 Fin15AnchoredAtom3643 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 12, 13}, {1, 3, 6, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29391 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2846 Fin15AnchoredAtom2848 Fin15AnchoredAtom2875
    Fin15AnchoredAtom2984 Fin15AnchoredAtom3149 Fin15AnchoredAtom3644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 12, 14}, {1, 3, 6, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29392 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2847 Fin15AnchoredAtom2848 Fin15AnchoredAtom2876
    Fin15AnchoredAtom2985 Fin15AnchoredAtom3150 Fin15AnchoredAtom3645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 13, 14}, {1, 3, 6, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29393 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2851 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2992 Fin15AnchoredAtom3157 Fin15AnchoredAtom3652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 2, 7, 9, 10}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29394 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2853 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2994 Fin15AnchoredAtom3159 Fin15AnchoredAtom3654 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 2, 7, 9, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29395 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2854 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2995 Fin15AnchoredAtom3160 Fin15AnchoredAtom3655 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 2, 7, 9, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29396 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2850 Fin15AnchoredAtom2855 Fin15AnchoredAtom2866
    Fin15AnchoredAtom2996 Fin15AnchoredAtom3161 Fin15AnchoredAtom3656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 2, 7, 9, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29397 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2851 Fin15AnchoredAtom2853 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2998 Fin15AnchoredAtom3163 Fin15AnchoredAtom3658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29398 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2851 Fin15AnchoredAtom2854 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2999 Fin15AnchoredAtom3164 Fin15AnchoredAtom3659 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29399 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2851 Fin15AnchoredAtom2855 Fin15AnchoredAtom2870
    Fin15AnchoredAtom3000 Fin15AnchoredAtom3165 Fin15AnchoredAtom3660 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29400 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2853 Fin15AnchoredAtom2854 Fin15AnchoredAtom2874
    Fin15AnchoredAtom3004 Fin15AnchoredAtom3169 Fin15AnchoredAtom3664 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29401 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2853 Fin15AnchoredAtom2855 Fin15AnchoredAtom2875
    Fin15AnchoredAtom3005 Fin15AnchoredAtom3170 Fin15AnchoredAtom3665 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29402 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2854 Fin15AnchoredAtom2855 Fin15AnchoredAtom2876
    Fin15AnchoredAtom3006 Fin15AnchoredAtom3171 Fin15AnchoredAtom3666 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29403 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2862 Fin15AnchoredAtom2864 Fin15AnchoredAtom2868
    Fin15AnchoredAtom3023 Fin15AnchoredAtom3188 Fin15AnchoredAtom3683 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 2, 9, 10, 12}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29404 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2862 Fin15AnchoredAtom2865 Fin15AnchoredAtom2869
    Fin15AnchoredAtom3024 Fin15AnchoredAtom3189 Fin15AnchoredAtom3684 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 2, 9, 10, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29405 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2862 Fin15AnchoredAtom2866 Fin15AnchoredAtom2870
    Fin15AnchoredAtom3025 Fin15AnchoredAtom3190 Fin15AnchoredAtom3685 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 2, 9, 10, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29406 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2864 Fin15AnchoredAtom2865 Fin15AnchoredAtom2874
    Fin15AnchoredAtom3029 Fin15AnchoredAtom3194 Fin15AnchoredAtom3689 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29407 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2864 Fin15AnchoredAtom2866 Fin15AnchoredAtom2875
    Fin15AnchoredAtom3030 Fin15AnchoredAtom3195 Fin15AnchoredAtom3690 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29408 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2865 Fin15AnchoredAtom2866 Fin15AnchoredAtom2876
    Fin15AnchoredAtom3031 Fin15AnchoredAtom3196 Fin15AnchoredAtom3691 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29409 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2868 Fin15AnchoredAtom2869 Fin15AnchoredAtom2874
    Fin15AnchoredAtom3035 Fin15AnchoredAtom3200 Fin15AnchoredAtom3695 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 2, 10, 12, 13}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29410 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2868 Fin15AnchoredAtom2870 Fin15AnchoredAtom2875
    Fin15AnchoredAtom3036 Fin15AnchoredAtom3201 Fin15AnchoredAtom3696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 2, 10, 12, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29411 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2869 Fin15AnchoredAtom2870 Fin15AnchoredAtom2876
    Fin15AnchoredAtom3037 Fin15AnchoredAtom3202 Fin15AnchoredAtom3697 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29412 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2874 Fin15AnchoredAtom2875 Fin15AnchoredAtom2876
    Fin15AnchoredAtom3041 Fin15AnchoredAtom3206 Fin15AnchoredAtom3701 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 3, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 2, 12, 13, 14}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29413 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2878 Fin15AnchoredAtom2886
    Fin15AnchoredAtom2922 Fin15AnchoredAtom3207 Fin15AnchoredAtom3702 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 7}, {1, 4, 5, 6, 7}, {1, 2, 5, 6, 7}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29414 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2880 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2924 Fin15AnchoredAtom3209 Fin15AnchoredAtom3704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 9}, {1, 4, 5, 6, 9}, {1, 2, 5, 6, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29415 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2881 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2925 Fin15AnchoredAtom3210 Fin15AnchoredAtom3705 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 10}, {1, 4, 5, 6, 10}, {1, 2, 5, 6, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29416 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2883 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2927 Fin15AnchoredAtom3212 Fin15AnchoredAtom3707 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 12}, {1, 4, 5, 6, 12}, {1, 2, 5, 6, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29417 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2884 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2928 Fin15AnchoredAtom3213 Fin15AnchoredAtom3708 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 13}, {1, 4, 5, 6, 13}, {1, 2, 5, 6, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29418 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2877 Fin15AnchoredAtom2885 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2929 Fin15AnchoredAtom3214 Fin15AnchoredAtom3709 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 14}, {1, 4, 5, 6, 14}, {1, 2, 5, 6, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29419 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2880 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2931 Fin15AnchoredAtom3216 Fin15AnchoredAtom3711 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 9}, {1, 4, 5, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29420 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2881 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2932 Fin15AnchoredAtom3217 Fin15AnchoredAtom3712 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 10}, {1, 4, 5, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29421 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2883 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2934 Fin15AnchoredAtom3219 Fin15AnchoredAtom3714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 12}, {1, 4, 5, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29422 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2884 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2935 Fin15AnchoredAtom3220 Fin15AnchoredAtom3715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 13}, {1, 4, 5, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29423 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2878 Fin15AnchoredAtom2885 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2936 Fin15AnchoredAtom3221 Fin15AnchoredAtom3716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 14}, {1, 4, 5, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29424 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2881 Fin15AnchoredAtom2907
    Fin15AnchoredAtom2943 Fin15AnchoredAtom3228 Fin15AnchoredAtom3723 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 10}, {1, 4, 5, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29425 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2882 chi ∧
      Fin15AnchoredAtom2908 chi ∧
      Fin15AnchoredAtom2944 chi ∧
      Fin15AnchoredAtom3229 chi ∧
      Fin15AnchoredAtom3724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2882 Fin15AnchoredAtom2908
    Fin15AnchoredAtom2944 Fin15AnchoredAtom3229 Fin15AnchoredAtom3724 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 11}, {1, 4, 5, 9, 11}, {1, 2, 5, 9, 11}, {1, 2, 4, 9, 11}, {1, 2, 4, 5, 11}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29426 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2883 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2945 Fin15AnchoredAtom3230 Fin15AnchoredAtom3725 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 12}, {1, 4, 5, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29427 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2884 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2946 Fin15AnchoredAtom3231 Fin15AnchoredAtom3726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 13}, {1, 4, 5, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29428 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2880 Fin15AnchoredAtom2885 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2947 Fin15AnchoredAtom3232 Fin15AnchoredAtom3727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 14}, {1, 4, 5, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29429 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2881 Fin15AnchoredAtom2883 Fin15AnchoredAtom2913
    Fin15AnchoredAtom2949 Fin15AnchoredAtom3234 Fin15AnchoredAtom3729 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 12}, {1, 4, 5, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29430 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2881 Fin15AnchoredAtom2884 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2950 Fin15AnchoredAtom3235 Fin15AnchoredAtom3730 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 13}, {1, 4, 5, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29431 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2881 Fin15AnchoredAtom2885 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3236 Fin15AnchoredAtom3731 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 14}, {1, 4, 5, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29432 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2883 Fin15AnchoredAtom2884 Fin15AnchoredAtom2919
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3240 Fin15AnchoredAtom3735 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 12, 13}, {1, 4, 5, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29433 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2883 Fin15AnchoredAtom2885 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3241 Fin15AnchoredAtom3736 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 12, 14}, {1, 4, 5, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29434 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2884 Fin15AnchoredAtom2885 Fin15AnchoredAtom2921
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3242 Fin15AnchoredAtom3737 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 13, 14}, {1, 4, 5, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29435 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2888 Fin15AnchoredAtom2895
    Fin15AnchoredAtom2959 Fin15AnchoredAtom3244 Fin15AnchoredAtom3739 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 2, 6, 7, 9}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29436 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2889 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2960 Fin15AnchoredAtom3245 Fin15AnchoredAtom3740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 2, 6, 7, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29437 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2891 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2962 Fin15AnchoredAtom3247 Fin15AnchoredAtom3742 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 2, 6, 7, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29438 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2892 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2963 Fin15AnchoredAtom3248 Fin15AnchoredAtom3743 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 2, 6, 7, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29439 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2886 Fin15AnchoredAtom2893 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2964 Fin15AnchoredAtom3249 Fin15AnchoredAtom3744 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 2, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 2, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 2, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 2, 6, 7, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
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
