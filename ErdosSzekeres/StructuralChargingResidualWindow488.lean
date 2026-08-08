module

public import ErdosSzekeres.StructuralChargingCupBlocks67Symbolic

@[expose] public section

/-!
# Closure of the residual `(4,8,8)` critical-root window

The ordered `6+7` cup-block theorem bounds the upper child of an open critical
root by twelve vertices.  At exact total size twenty-three, the remaining
positive upper sizes fall into three regimes.  Elementary cup--cap thresholds
supply crossing cup/cap pairs `(5,3)`, `(6,2)`, or `(7,1)`, closing the full
`(4,8,8)` root transition unconditionally.  The published-index normal form
and its predecessor-conditional proof are retained as reusable alternative
machinery for the higher fixed-`k=8` states.
-/

namespace ErdosSzekeres

/-- Every finite set with at least two vertices contains a two-vertex cap.
The cap condition is vacuous because an ordered triple cannot lie in a
two-element set. -/
theorem containsCapSet_two {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} (hcard : 2 ≤ s.card) : ContainsCapSet χ s 2 := by
  obtain ⟨pair, hpairSub, hpairCard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨pair, hpairSub, hpairCard, ?_⟩
  intro t hi hj hk
  have htripleSub : {t.i, t.j, t.k} ⊆ pair := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hi, hj, hk⟩
  have htripleCard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
    simp [ne_of_lt t.hij, ne_of_lt t.hjk,
      ne_of_lt (t.hij.trans t.hjk)]
  have := Finset.card_le_card htripleSub
  rw [htripleCard, hpairCard] at this
  omega

/-- Sixteen vertices satisfying the one-change law and avoiding a four-cap
contain a six-cup. -/
theorem containsCupSix_of_oneChange_no_capFour_card_ge_sixteen
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hcard : 16 ≤ s.card) : ContainsCupSet χ s 6 := by
  rcases containsCapFour_or_containsCupSix_of_oneChange_card_gt_fifteen
      hone (by omega) with hcap | hcup
  · exact (hnoCap hcap).elim
  · exact hcup

/-- Eight vertices satisfying the one-change law contain a three-cap or an
eight-cup.  This is the `(3,8)` cup--cap recurrence, with the eight-chain
promoted from consecutive turns by the one-change law. -/
theorem containsCapThree_or_containsCupEight_of_oneChange_card_ge_eight
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 8 ≤ s.card) :
    ContainsCapSet χ s 3 ∨ ContainsCupSet χ s 8 := by
  have hchoose : Nat.choose (1 + 6) 1 < s.card := by
    norm_num [Nat.choose]
    omega
  rcases CupCap.cup_cap (CupCap.totalColor χ) 1 6 s hchoose with hcap | hcup
  · obtain ⟨l, hchain, hlen, hlin⟩ := hcap
    norm_num at hlen
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 3 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 3 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.right := by
      have ht : CupCap.totalColor χ (f 0) (f 1) (f 2) = Turn.right := by
        simpa [f, idx, g] using h012'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    refine Or.inl ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · apply FinsetPolygon.IsCap.image
      refine ⟨f.strictMono, ?_⟩
      intro i j k hij hjk
      have hi : i = 0 := by omega
      have hj : j = 1 := by omega
      have hk : k = 2 := by omega
      subst i
      subst j
      subst k
      exact h012
  · obtain ⟨l, hchain, hlen, hlin⟩ := hcup
    norm_num at hlen
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 8 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 8 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h234' := CupCap.consecutive'_getElem hchain.2 2 (by omega)
    have h345' := CupCap.consecutive'_getElem hchain.2 3 (by omega)
    have h456' := CupCap.consecutive'_getElem hchain.2 4 (by omega)
    have h567' := CupCap.consecutive'_getElem hchain.2 5 (by omega)
    have h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 0) (f 1) (f 2) = Turn.left := by
        simpa [f, idx, g] using h012'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 1) (f 2) (f 3) = Turn.left := by
        simpa [f, idx, g] using h123'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 2) (f 3) (f 4) = Turn.left := by
        simpa [f, idx, g] using h234'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 3) (f 4) (f 5) = Turn.left := by
        simpa [f, idx, g] using h345'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h456 : χ ⟨f 4, f 5, f 6, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 4) (f 5) (f 6) = Turn.left := by
        simpa [f, idx, g] using h456'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h567 : χ ⟨f 5, f 6, f 7, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 5) (f 6) (f 7) = Turn.left := by
        simpa [f, idx, g] using h567'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    refine Or.inr ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCup.image
        (isMonochromaticChain_finEight_of_consecutive f
          (hone.mono hfsub) h012 h123 h234 h345 h456 h567)

/-- A one-change set of at least eight vertices avoiding an eight-cup
contains a three-cap. -/
theorem containsCapThree_of_oneChange_no_cupEight_card_ge_eight
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCup : ¬ContainsCupSet χ s 8)
    (hcard : 8 ≤ s.card) : ContainsCapSet χ s 3 := by
  rcases containsCapThree_or_containsCupEight_of_oneChange_card_ge_eight
      hone hcard with hcap | hcup
  · exact hcap
  · exact (hnoCup hcup).elim

/-- Twenty-two vertices satisfying the one-change law contain a four-cap or
a seven-cup.  This is the `(4,7)` cup--cap threshold. -/
theorem containsCapFour_or_containsCupSeven_of_oneChange_card_ge_twentyTwo
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 22 ≤ s.card) :
    ContainsCapSet χ s 4 ∨ ContainsCupSet χ s 7 := by
  have hchoose : Nat.choose (2 + 5) 2 < s.card := by
    norm_num [Nat.choose]
    omega
  rcases CupCap.cup_cap (CupCap.totalColor χ) 2 5 s hchoose with hcap | hcup
  · obtain ⟨l, hchain, hlen, hlin⟩ := hcap
    norm_num at hlen
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 4 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 4 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.right := by
      have ht : CupCap.totalColor χ (f 0) (f 1) (f 2) = Turn.right := by
        simpa [f, idx, g] using h012'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.right := by
      have ht : CupCap.totalColor χ (f 1) (f 2) (f 3) = Turn.right := by
        simpa [f, idx, g] using h123'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    refine Or.inl ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCap.image
        (isMonochromaticChain_finFour_of_outer_eq f
          (hone.mono hfsub) h012 h123)
  · obtain ⟨l, hchain, hlen, hlin⟩ := hcup
    norm_num at hlen
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 7 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 7 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h234' := CupCap.consecutive'_getElem hchain.2 2 (by omega)
    have h345' := CupCap.consecutive'_getElem hchain.2 3 (by omega)
    have h456' := CupCap.consecutive'_getElem hchain.2 4 (by omega)
    have h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 0) (f 1) (f 2) = Turn.left := by
        simpa [f, idx, g] using h012'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 1) (f 2) (f 3) = Turn.left := by
        simpa [f, idx, g] using h123'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 2) (f 3) (f 4) = Turn.left := by
        simpa [f, idx, g] using h234'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 3) (f 4) (f 5) = Turn.left := by
        simpa [f, idx, g] using h345'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h456 : χ ⟨f 4, f 5, f 6, by simp, by simp⟩ = Turn.left := by
      have ht : CupCap.totalColor χ (f 4) (f 5) (f 6) = Turn.left := by
        simpa [f, idx, g] using h456'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    refine Or.inr ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCup.image
        (isMonochromaticChain_finSeven_of_consecutive f
          (hone.mono hfsub) h012 h123 h234 h345 h456)

/-- A one-change set of at least twenty-two vertices avoiding a four-cap
contains a seven-cup. -/
theorem containsCupSeven_of_oneChange_no_capFour_card_ge_twentyTwo
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hcard : 22 ≤ s.card) : ContainsCupSet χ s 7 := by
  rcases containsCapFour_or_containsCupSeven_of_oneChange_card_ge_twentyTwo
      hone hcard with hcap | hcup
  · exact (hnoCap hcap).elim
  · exact hcup

/-- Every positive split of twenty-three with upper part at most twelve has
published `(4,8,8)` auxiliary indices summing to eight. -/
theorem published_indices_add_eq_eight_at_488_residual
    {lowerCard upperCard : ℕ}
    (htotal : lowerCard + upperCard = decomposableThreshold 4 8 8 + 1)
    (hupperPos : 0 < upperCard) (hupperBound : upperCard ≤ 12) :
    publishedChildIndex 4 8 8 lowerCard +
        publishedCapChildIndex 4 8 8 upperCard = 8 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top] at htotal
  have hlower : lowerCard = 23 - upperCard := by omega
  interval_cases upperCard <;>
    norm_num at hlower <;> subst lowerCard <;>
    norm_num [publishedChildIndex, publishedCapChildIndex,
      decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top] at *

/-- The exact `(4,8,8)` critical root is impossible.  The proved upper-child
bound leaves three cardinality regimes.  Elementary cup--cap thresholds
supply crossing cup/cap pairs of sizes `(5,3)`, `(6,2)`, or `(7,1)`; every
pair glues across the deep-below split to a strong eight-set. -/
theorem criticalRootImpossible_488 :
    DecomposableCriticalRootImpossible 4 8 8 := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  have hthreshold : decomposableThreshold 4 8 8 = 22 := by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  have htotal : lower.card + upper.card = 23 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    simpa [hthreshold] using hcard
  have hlowerPos : 0 < lower.card := by
    rw [hthreshold] at hupperBound
    omega
  have hupperPos : 0 < upper.card := by
    rw [hthreshold] at hlowerBound
    omega
  have hlowerNonempty : lower.Nonempty := Finset.card_pos.mp hlowerPos
  have hupperNonempty : upper.Nonempty := Finset.card_pos.mp hupperPos
  have hupperTwelve : upper.card ≤ 12 :=
    upper_card_le_twelve_at_open_488 hlowerNonempty hupper hdeep
      hnoCap hnoCup hnoStrong
  have hlowerOne : OneChangeOn χ lower := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hlower.turnSequenceAllowed hij hjk hkl hi hj hk hl
  have hupperOne : OneChangeOn χ upper := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupper.turnSequenceAllowed hij hjk hkl hi hj hk hl
  have hnoCapLower : ¬ContainsCapSet χ lower 4 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      Finset.subset_union_left)
  have hnoCupUpper : ¬ContainsCupSet χ upper 8 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
      Finset.subset_union_right)
  by_cases hupperEight : 8 ≤ upper.card
  · have hlowerEleven : 11 ≤ lower.card := by omega
    have hlowerCup :=
      containsCupFive_of_oneChange_no_capFour_card_ge_eleven
        hlowerOne hnoCapLower hlowerEleven
    have hupperCap :=
      containsCapThree_of_oneChange_no_cupEight_card_ge_eight
        hupperOne hnoCupUpper hupperEight
    exact hnoStrong
      (hdeep.containsStrongPolygonSet_of_containsCupCap
        hlowerCup hupperCap (by omega))
  · by_cases hupperTwo : 2 ≤ upper.card
    · have hlowerSixteen : 16 ≤ lower.card := by omega
      have hlowerCup :=
        containsCupSix_of_oneChange_no_capFour_card_ge_sixteen
          hlowerOne hnoCapLower hlowerSixteen
      have hupperCap := containsCapSet_two (χ := χ) hupperTwo
      exact hnoStrong
        (hdeep.containsStrongPolygonSet_of_containsCupCap
          hlowerCup hupperCap (by omega))
    · have hupperOneCard : upper.card = 1 := by omega
      have hlowerTwentyTwo : 22 ≤ lower.card := by omega
      have hlowerCup :=
        containsCupSeven_of_oneChange_no_capFour_card_ge_twentyTwo
          hlowerOne hnoCapLower hlowerTwentyTwo
      have hupperCap := containsCapSet_one (χ := χ) hupperNonempty
      exact hnoStrong
        (hdeep.containsStrongPolygonSet_of_containsCupCap
          hlowerCup hupperCap (by omega))

/-- The unconditional root closure lifts through the hereditary root
transition to the full decomposable `(4,8,8)` state. -/
theorem decomposableStateUpper_488 : DecomposableStateUpper 4 8 8 := by
  apply rootTransitionUpper_implies_decomposableStateUpper (by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top])
  apply criticalRootImpossible_implies_rootTransitionUpper
  exact criticalRootImpossible_488

/-- The proved cup-block gate closes the exact `(4,8,8)` critical root once
all strict predecessor states at fixed strong-polygon parameter eight are
available. -/
theorem criticalRootImpossible_488_of_predecessors
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8) :
    DecomposableCriticalRootImpossible 4 8 8 := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  have hthreshold : decomposableThreshold 4 8 8 = 22 := by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  have htotal : lower.card + upper.card = 23 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    simpa [hthreshold] using hcard
  have hlowerPos : 0 < lower.card := by
    rw [hthreshold] at hupperBound
    omega
  have hupperPos : 0 < upper.card := by
    rw [hthreshold] at hlowerBound
    omega
  have hlowerNonempty : lower.Nonempty := Finset.card_pos.mp hlowerPos
  have hupperNonempty : upper.Nonempty := Finset.card_pos.mp hupperPos
  have hupperTwelve : upper.card ≤ 12 :=
    upper_card_le_twelve_at_open_488 hlowerNonempty hupper hdeep
      hnoCap hnoCup hnoStrong
  obtain ⟨lowerSlice⟩ := exists_publishedChildSlice
    (a := 4) (u := 8) (k := 8) (child := lower) (by omega) hlowerNonempty
  obtain ⟨upperSlice, _⟩ := exists_publishedCapChildSlice_core_superset
    (a := 4) (u := 8) (k := 8) (child := upper) (seed := ∅)
      (by omega) hupperNonempty (by simp) (by simp)
  have hindexLe := published_slice_indices_add_le_of_predecessors
    lowerSlice upperSlice hlowerNonempty hupperNonempty hlower hupper hdeep
    hlowerBound hupperBound (by
      intro a u hau
      exact hpredecessors a u (by omega)) hnoCap hnoCup hnoStrong
  have hindexEq := published_indices_add_eq_eight_at_488_residual
    htotal hupperPos hupperTwelve
  rw [lowerSlice.index_eq, upperSlice.index_eq] at hindexLe
  omega

/-- Root-local closure lifts to the hereditary `(4,8,8)` state under the same
strict-predecessor hypothesis. -/
theorem decomposableStateUpper_488_of_predecessors
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8) :
    DecomposableStateUpper 4 8 8 := by
  apply rootTransitionUpper_implies_decomposableStateUpper (by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top])
  apply criticalRootImpossible_implies_rootTransitionUpper
  exact criticalRootImpossible_488_of_predecessors hpredecessors

end ErdosSzekeres

end
