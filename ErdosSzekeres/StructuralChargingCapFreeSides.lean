module

public import ErdosSzekeres.StructuralChargingCupBlocks56

@[expose] public section

/-!
# Four-cap-free gap sides

This file begins the conceptual proof of the `(5,6,7)` two-side bound.  It
uses the classical cup--cap recurrence at `(4,6)` and the rank-three
one-change law to bound either four-cap-free, six-cup-free side by fifteen.
Thus any counterexample to the sharp total bound 21 must have both sides in
the finite cardinality window 7 through 15.
-/

namespace ErdosSzekeres

/-- Exact local quantitative gate at `(5,6,7)`. Two ordered sides of a cut,
each avoiding a four-cap, contain at most 21 vertices when their union
satisfies the one-change law and avoids the three parent outcomes. -/
def TwoCapFreeSidesBound567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      left.card + right.card ≤ 21

/-- The ordinary `(4,6)` cup--cap threshold remains valid under the abstract
one-change law.  The generic recurrence first supplies a consecutive chain;
the fixed-size one-change lemmas promote it to an all-triples cap or cup. -/
theorem containsCapFour_or_containsCupSix_of_oneChange_card_gt_fifteen
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 15 < s.card) :
    ContainsCapSet χ s 4 ∨ ContainsCupSet χ s 6 := by
  have hchoose : Nat.choose (2 + 4) 2 < s.card := by
    norm_num [Nat.choose]
    exact hcard
  rcases CupCap.cup_cap (CupCap.totalColor χ) 2 4 s hchoose with hcap | hcup
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
    let idx : Fin 6 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 6 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h234' := CupCap.consecutive'_getElem hchain.2 2 (by omega)
    have h345' := CupCap.consecutive'_getElem hchain.2 3 (by omega)
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
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    refine Or.inr ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · exact FinsetPolygon.IsCup.image
        (isMonochromaticChain_finSix_of_consecutive f
          (hone.mono hfsub) h012 h123 h234 h345)

/-- A one-change set avoiding a four-cap and six-cup has at most fifteen
vertices. -/
theorem card_le_fifteen_of_oneChange_no_capFour_no_cupSix
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hnoCup : ¬ContainsCupSet χ s 6) : s.card ≤ 15 := by
  by_contra hcard
  rcases containsCapFour_or_containsCupSix_of_oneChange_card_gt_fifteen
      hone (by omega) with hcap | hcup
  · exact hnoCap hcap
  · exact hnoCup hcup

/-- Seven vertices satisfying the one-change law contain a four-cap or a
four-cup.  This is the `(4,4)` cup--cap recurrence, with the consecutive chain
promoted by the one-change law. -/
theorem containsCapFour_or_containsCupFour_of_oneChange_card_ge_seven
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 7 ≤ s.card) :
    ContainsCapSet χ s 4 ∨ ContainsCupSet χ s 4 := by
  have promoteFour (c : Turn)
      (h : CupCap.HasNChain (CupCap.totalColor χ) c 4 s) :
      ∃ f : Fin 4 ↪o Fin n, Finset.univ.image f ⊆ s ∧
        IsMonochromaticChain χ c f := by
    obtain ⟨l, hchain, hlen, hlin⟩ := h
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 4 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 4 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c := by
      have ht : CupCap.totalColor χ (f 0) (f 1) (f 2) = c := by
        simpa [f, idx, g] using h012'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c := by
      have ht : CupCap.totalColor χ (f 1) (f 2) (f 3) = c := by
        simpa [f, idx, g] using h123'
      rw [CupCap.totalColor_of_lt χ (by simp) (by simp)] at ht
      exact ht
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    exact ⟨f, hfsub,
      isMonochromaticChain_finFour_of_outer_eq f
        (hone.mono hfsub) h012 h123⟩
  have hchoose : Nat.choose (2 + 2) 2 < s.card := by
    norm_num [Nat.choose]
    omega
  rcases CupCap.cup_cap (CupCap.totalColor χ) 2 2 s hchoose with hcap | hcup
  · obtain ⟨f, hfsub, hf⟩ := promoteFour Turn.right (by simpa using hcap)
    exact Or.inl ⟨Finset.univ.image f, hfsub,
      by simpa using Finset.card_image_of_injective Finset.univ f.injective,
      FinsetPolygon.IsCap.image hf⟩
  · obtain ⟨f, hfsub, hf⟩ := promoteFour Turn.left (by simpa using hcup)
    exact Or.inr ⟨Finset.univ.image f, hfsub,
      by simpa using Finset.card_image_of_injective Finset.univ f.injective,
      FinsetPolygon.IsCup.image hf⟩

/-- A four-cap-free one-change set of at least seven vertices contains a
four-cup. -/
theorem containsCupFour_of_oneChange_no_capFour_card_ge_seven
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hcard : 7 ≤ s.card) : ContainsCupSet χ s 4 := by
  rcases containsCapFour_or_containsCupFour_of_oneChange_card_ge_seven
      hone hcard with hcap | hcup
  · exact (hnoCap hcap).elim
  · exact hcup

/-- Eleven vertices satisfying the one-change law contain a four-cap or a
five-cup. -/
theorem containsCapFour_or_containsCupFive_of_oneChange_card_ge_eleven
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 11 ≤ s.card) :
    ContainsCapSet χ s 4 ∨ ContainsCupSet χ s 5 := by
  have hchoose : Nat.choose (2 + 3) 2 < s.card := by
    norm_num [Nat.choose]
    omega
  rcases CupCap.cup_cap (CupCap.totalColor χ) 2 3 s hchoose with hcap | hcup
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
    exact Or.inl ⟨Finset.univ.image f, hfsub,
      by simpa using Finset.card_image_of_injective Finset.univ f.injective,
      FinsetPolygon.IsCap.image
        (isMonochromaticChain_finFour_of_outer_eq f
          (hone.mono hfsub) h012 h123)⟩
  · obtain ⟨l, hchain, hlen, hlin⟩ := hcup
    norm_num at hlen
    let g : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    let idx : Fin 5 ↪o Fin l.length :=
      (Fin.castOrderIso hlen.symm).toOrderEmbedding
    let f : Fin 5 ↪o Fin n := idx.trans g
    have h012' := CupCap.consecutive'_getElem hchain.2 0 (by omega)
    have h123' := CupCap.consecutive'_getElem hchain.2 1 (by omega)
    have h234' := CupCap.consecutive'_getElem hchain.2 2 (by omega)
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
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa [f, idx, g] using hlin (l.get (idx i)) (l.get_mem (idx i))
    exact Or.inr ⟨Finset.univ.image f, hfsub,
      by simpa using Finset.card_image_of_injective Finset.univ f.injective,
      FinsetPolygon.IsCup.image
        (isMonochromaticChain_finFive_of_consecutive f
          (hone.mono hfsub) h012 h123 h234)⟩

/-- A four-cap-free one-change set of at least eleven vertices contains a
five-cup. -/
theorem containsCupFive_of_oneChange_no_capFour_card_ge_eleven
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hcard : 11 ≤ s.card) : ContainsCupSet χ s 5 := by
  rcases containsCapFour_or_containsCupFive_of_oneChange_card_ge_eleven
      hone hcard with hcap | hcup
  · exact (hnoCap hcap).elim
  · exact hcup

/-- In the proposed two-side gate, the elementary cup--cap theorem bounds
both sides separately by fifteen. -/
theorem two_cap_free_sides_individual_card_le_fifteen
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6) :
    left.card ≤ 15 ∧ right.card ≤ 15 := by
  constructor
  · apply card_le_fifteen_of_oneChange_no_capFour_no_cupSix
      (hone.mono Finset.subset_union_left) hleftCap
    intro hcup
    exact hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_left)
  · apply card_le_fifteen_of_oneChange_no_capFour_no_cupSix
      (hone.mono Finset.subset_union_right) hrightCap
    intro hcup
    exact hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right)

/-- Consequently every counterexample to the proposed sharp total bound has
both side cardinalities in the residual interval `[7,15]`. -/
theorem two_cap_free_sides_counterexample_card_window
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hlarge : 21 < left.card + right.card) :
    7 ≤ left.card ∧ left.card ≤ 15 ∧ 7 ≤ right.card ∧ right.card ≤ 15 := by
  have hbounds := two_cap_free_sides_individual_card_le_fifteen
    hone hleftCap hrightCap hnoCup
  omega

/-- Every pair in the residual cardinality window carries an explicit
four-cup on each side of the cut. -/
theorem two_cap_free_sides_have_cupFour
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hleftCard : 7 ≤ left.card) (hrightCard : 7 ≤ right.card) :
    ContainsCupSet χ left 4 ∧ ContainsCupSet χ right 4 := by
  constructor
  · exact containsCupFour_of_oneChange_no_capFour_card_ge_seven
      (hone.mono Finset.subset_union_left) hleftCap hleftCard
  · exact containsCupFour_of_oneChange_no_capFour_card_ge_seven
      (hone.mono Finset.subset_union_right) hrightCap hrightCard

/-- At total cardinality at least 22, the two sides carry ordered cup blocks
of sizes four and five in one of the two orientations. -/
theorem two_cap_free_sides_have_cupFour_cupFive
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hleftCard : 7 ≤ left.card) (hrightCard : 7 ≤ right.card)
    (htotal : 22 ≤ left.card + right.card) :
    (ContainsCupSet χ left 4 ∧ ContainsCupSet χ right 5) ∨
      (ContainsCupSet χ left 5 ∧ ContainsCupSet χ right 4) := by
  have hcupsFour := two_cap_free_sides_have_cupFour
    hone hleftCap hrightCap hleftCard hrightCard
  by_cases hleftLarge : 11 ≤ left.card
  · exact Or.inr ⟨
      containsCupFive_of_oneChange_no_capFour_card_ge_eleven
        (hone.mono Finset.subset_union_left) hleftCap hleftLarge,
      hcupsFour.2⟩
  · have hrightLarge : 11 ≤ right.card := by omega
    exact Or.inl ⟨hcupsFour.1,
      containsCupFive_of_oneChange_no_capFour_card_ge_eleven
        (hone.mono Finset.subset_union_right) hrightCap hrightLarge⟩

/-- The existing symbolic `4+5/5+4` theorem converts the residual cardinality
window into a crossing four-cap or a strong six-set.  The six-cup branch is
excluded by the ambient hypothesis. -/
theorem two_cap_free_sides_contains_capFour_or_strongSix
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hleftCard : 7 ≤ left.card) (hrightCard : 7 ≤ right.card)
    (htotal : 22 ≤ left.card + right.card)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 6 := by
  rcases two_cap_free_sides_have_cupFour_cupFive hone hleftCap hrightCap
      hleftCard hrightCard htotal with hcups | hcups
  · obtain ⟨leftCup, hleftSub, hleftCupCard, hleftCup⟩ := hcups.1
    obtain ⟨rightCup, hrightSub, hrightCupCard, hrightCup⟩ := hcups.2
    have hwSub : leftCup ∪ rightCup ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases cupBlocks45Force466
        (hdisjoint.mono hleftSub hrightSub)
        (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
        (Or.inl ⟨hleftCupCard, hrightCupCard⟩)
        hleftCup hrightCup (hone.mono hwSub) with hcap | hcup | hstrong
    · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap hwSub)
    · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hwSub)).elim
    · exact Or.inr
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hwSub)
  · obtain ⟨leftCup, hleftSub, hleftCupCard, hleftCup⟩ := hcups.1
    obtain ⟨rightCup, hrightSub, hrightCupCard, hrightCup⟩ := hcups.2
    have hwSub : leftCup ∪ rightCup ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases cupBlocks45Force466
        (hdisjoint.mono hleftSub hrightSub)
        (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
        (Or.inr ⟨hleftCupCard, hrightCupCard⟩)
        hleftCup hrightCup (hone.mono hwSub) with hcap | hcup | hstrong
    · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap hwSub)
    · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hwSub)).elim
    · exact Or.inr
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hwSub)

/-- A four-cap in the union of two four-cap-free sides must meet both sides. -/
theorem capFour_witness_meets_both_cap_free_sides
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hcap : ContainsCapSet χ (left ∪ right) 4) :
    ∃ cap : Finset (Fin n), cap ⊆ left ∪ right ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ (cap ∩ left).Nonempty ∧ (cap ∩ right).Nonempty := by
  obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ := hcap
  have hleftMeet : (cap ∩ left).Nonempty := by
    by_contra hnot
    have hcapSubRight : cap ⊆ right := by
      intro x hx
      rcases Finset.mem_union.mp (hcapSub hx) with hxLeft | hxRight
      · exact (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hxLeft⟩⟩).elim
      · exact hxRight
    exact hrightCap ⟨cap, hcapSubRight, hcapCard, hcapSet⟩
  have hrightMeet : (cap ∩ right).Nonempty := by
    by_contra hnot
    have hcapSubLeft : cap ⊆ left := by
      intro x hx
      rcases Finset.mem_union.mp (hcapSub hx) with hxLeft | hxRight
      · exact hxLeft
      · exact (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hxRight⟩⟩).elim
    exact hleftCap ⟨cap, hcapSubLeft, hcapCard, hcapSet⟩
  exact ⟨cap, hcapSub, hcapCard, hcapSet, hleftMeet, hrightMeet⟩

/-- Witness-level form of the first cross-gap charge: in the residual window
there is either an actual four-cap meeting both sides or a strong six-set. -/
theorem two_cap_free_sides_contains_crossing_capFour_or_strongSix
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hleftCard : 7 ≤ left.card) (hrightCard : 7 ≤ right.card)
    (htotal : 22 ≤ left.card + right.card)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6) :
    (∃ cap : Finset (Fin n), cap ⊆ left ∪ right ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ (cap ∩ left).Nonempty ∧ (cap ∩ right).Nonempty) ∨
      ContainsStrongPolygonSet χ (left ∪ right) 6 := by
  rcases two_cap_free_sides_contains_capFour_or_strongSix hdisjoint horder
      hone hleftCap hrightCap hleftCard hrightCard htotal hnoCup with
      hcap | hstrong
  · exact Or.inl
      (capFour_witness_meets_both_cap_free_sides hleftCap hrightCap hcap)
  · exact Or.inr hstrong

/-- A local certificate that adjoining `q` to a cap fails to produce the next
cap size. The bad triple is required to use `q`; triples internal to `cap`
cannot be bad. -/
def HasCapExtensionFailure {n : ℕ} (χ : TripleColoring n)
    (cap : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ t : OrderedTriple n,
    t.i ∈ insert q cap ∧ t.j ∈ insert q cap ∧ t.k ∈ insert q cap ∧
      χ t = Turn.left ∧ (t.i = q ∨ t.j = q ∨ t.k = q)

/-- A local certificate that adjoining `q` to a strong polygon fails the
four-index consistency law. The bad quadruple is required to use `q`. -/
def HasStrongExtensionFailure {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l),
    i ∈ insert q polygon ∧ j ∈ insert q polygon ∧
      k ∈ insert q polygon ∧ l ∈ insert q polygon ∧
      (i = q ∨ j = q ∨ k = q ∨ l = q) ∧
      ¬(χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
        χ ⟨i, k, l, hij.trans hjk, hkl⟩ = χ ⟨j, k, l, hjk, hkl⟩)

/-- Every ambient vertex outside an `a`-cap has a local obstruction when the
ambient set contains no `(a+1)`-cap. -/
theorem cap_extension_failure_of_no_cap_succ
    {n a : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = a)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient) (hqCap : q ∉ cap)
    (hnoCap : ¬ContainsCapSet χ ambient (a + 1)) :
    HasCapExtensionFailure χ cap q := by
  classical
  by_contra hfailure
  have hthroughQ : ∀ t : OrderedTriple n,
      t.i ∈ insert q cap → t.j ∈ insert q cap → t.k ∈ insert q cap →
      (t.i = q ∨ t.j = q ∨ t.k = q) → χ t = Turn.right := by
    intro t hi hj hk hq
    cases hcolor : χ t with
    | left =>
        exact (hfailure ⟨t, hi, hj, hk, hcolor, hq⟩).elim
    | right => rfl
  have hcapInsert : IsCapSet χ (insert q cap) := by
    intro t hi hj hk
    by_cases hq : t.i = q ∨ t.j = q ∨ t.k = q
    · exact hthroughQ t hi hj hk hq
    · apply hcap t
      · rcases Finset.mem_insert.mp hi with hi | hi
        · exact (hq (Or.inl hi)).elim
        · exact hi
      · rcases Finset.mem_insert.mp hj with hj | hj
        · exact (hq (Or.inr (Or.inl hj))).elim
        · exact hj
      · rcases Finset.mem_insert.mp hk with hk | hk
        · exact (hq (Or.inr (Or.inr hk))).elim
        · exact hk
  apply hnoCap
  refine ⟨insert q cap, ?_, ?_, hcapInsert⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · exact hcapSub hx
  · rw [Finset.card_insert_of_notMem hqCap, hcapCard]

/-- For a four-cap, the local obstruction can be chosen among the three
consecutive triples of the sorted five-set.  A left-turning consecutive triple
must contain the adjoined vertex. -/
theorem cap_extension_failure_has_consecutive_witness
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient) (hqCap : q ∉ cap)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    ∃ f : Fin 5 ↪o Fin n,
      Finset.univ.image f = insert q cap ∧
      ((χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.left ∧
          (f 0 = q ∨ f 1 = q ∨ f 2 = q)) ∨
        (χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.left ∧
          (f 1 = q ∨ f 2 = q ∨ f 3 = q)) ∨
        (χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = Turn.left ∧
          (f 2 = q ∨ f 3 = q ∨ f 4 = q))) := by
  classical
  have hinsertCard : (insert q cap).card = 5 := by
    rw [Finset.card_insert_of_notMem hqCap, hcapCard]
  let f : Fin 5 ↪o Fin n := (insert q cap).orderEmbOfFin hinsertCard
  have hfmem (i : Fin 5) : f i ∈ insert q cap := by
    exact (insert q cap).orderEmbOfFin_mem hinsertCard i
  have himage : Finset.univ.image f = insert q cap := by
    apply Finset.image_orderEmbOfFin_univ
  have hinsertSub : insert q cap ⊆ ambient := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · exact hcapSub hx
  have q_mem_of_left (i j k : Fin 5) (hij : i < j) (hjk : j < k)
      (hleft : χ ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ =
        Turn.left) : f i = q ∨ f j = q ∨ f k = q := by
    by_contra hq
    push Not at hq
    have hiCap : f i ∈ cap := by
      rcases Finset.mem_insert.mp (hfmem i) with hi | hi
      · exact (hq.1 hi).elim
      · exact hi
    have hjCap : f j ∈ cap := by
      rcases Finset.mem_insert.mp (hfmem j) with hj | hj
      · exact (hq.2.1 hj).elim
      · exact hj
    have hkCap : f k ∈ cap := by
      rcases Finset.mem_insert.mp (hfmem k) with hk | hk
      · exact (hq.2.2 hk).elim
      · exact hk
    have hright := hcap
      ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩
      hiCap hjCap hkCap
    rw [hleft] at hright
    exact Turn.noConfusion hright
  refine ⟨f, himage, ?_⟩
  cases h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ with
  | left =>
      exact Or.inl
        ⟨rfl, q_mem_of_left 0 1 2 (by decide) (by decide) h012⟩
  | right =>
    cases h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ with
    | left =>
        exact Or.inr (Or.inl
          ⟨rfl, q_mem_of_left 1 2 3 (by decide) (by decide) h123⟩)
    | right =>
      cases h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ with
      | left =>
          exact Or.inr (Or.inr
            ⟨rfl, q_mem_of_left 2 3 4 (by decide) (by decide) h234⟩)
      | right =>
        exfalso
        apply hnoCap
        refine ⟨insert q cap, hinsertSub, hinsertCard, ?_⟩
        rw [← himage]
        apply FinsetPolygon.IsCap.image
        have honeImage : OneChangeOn χ (Finset.univ.image f) := by
          rw [himage]
          exact hone.mono hinsertSub
        apply isMonochromaticChain_finFive_of_consecutive f honeImage
        · simpa using h012
        · simpa using h123
        · simpa using h234

/-- If a five-cup lies wholly to the left of an ambient vertex, the triple
formed by its last two vertices and that vertex must turn right when ambient
six-cups are forbidden. -/
theorem cupFive_forces_right_bridge_of_no_cupSix
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (horder : ∀ x ∈ cup, x < y) (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    χ ⟨cup.orderEmbOfFin hcupCard 3, cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ = Turn.right := by
  let le : Fin 5 ↪o Fin n := cup.orderEmbOfFin hcupCard
  let f : Fin 6 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, y] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact horder _ (cup.orderEmbOfFin_mem hcupCard _))
  have hfmem : ∀ i : Fin 6, f i ∈ ambient := by
    intro i
    fin_cases i <;>
      simp [f, le, hyAmbient,
        hcupSub (cup.orderEmbOfFin_mem hcupCard _)]
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfmem i
  cases hbridge : χ ⟨cup.orderEmbOfFin hcupCard 3,
      cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ with
  | right => rfl
  | left =>
    exfalso
    apply hnoCup
    refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · apply FinsetPolygon.IsCup.image
      apply isMonochromaticChain_finSix_of_consecutive f (hone.mono hfsub)
      · simpa [f, le] using hcup _
          (cup.orderEmbOfFin_mem hcupCard 0)
          (cup.orderEmbOfFin_mem hcupCard 1)
          (cup.orderEmbOfFin_mem hcupCard 2)
      · simpa [f, le] using hcup _
          (cup.orderEmbOfFin_mem hcupCard 1)
          (cup.orderEmbOfFin_mem hcupCard 2)
          (cup.orderEmbOfFin_mem hcupCard 3)
      · simpa [f, le] using hcup _
          (cup.orderEmbOfFin_mem hcupCard 2)
          (cup.orderEmbOfFin_mem hcupCard 3)
          (cup.orderEmbOfFin_mem hcupCard 4)
      · simpa [f, le] using hbridge

/-- Bridge colors forced by a five-cup are nested: for two later vertices,
a left turn through the penultimate cup vertex forces the corresponding turn
through the last cup vertex to be left as well. -/
theorem cupFive_right_bridge_nesting
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y z : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (hzAmbient : z ∈ ambient) (horderY : ∀ x ∈ cup, x < y)
    (horderZ : ∀ x ∈ cup, x < z) (hyz : y < z)
    (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hleft : χ ⟨cup.orderEmbOfFin hcupCard 3, y, z,
      horderY _ (cup.orderEmbOfFin_mem hcupCard 3), hyz⟩ = Turn.left) :
    χ ⟨cup.orderEmbOfFin hcupCard 4, y, z,
      horderY _ (cup.orderEmbOfFin_mem hcupCard 4), hyz⟩ = Turn.left := by
  have hbridgeY := cupFive_forces_right_bridge_of_no_cupSix
    hcupSub hcupCard hcup hyAmbient horderY hone hnoCup
  have hbridgeZ := cupFive_forces_right_bridge_of_no_cupSix
    hcupSub hcupCard hcup hzAmbient horderZ hone hnoCup
  have hallowed := hone
    ((cup.orderEmbOfFin hcupCard).strictMono
      (show (3 : Fin 5) < 4 by decide))
    (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)) hyz
    (hcupSub (cup.orderEmbOfFin_mem hcupCard 3))
    (hcupSub (cup.orderEmbOfFin_mem hcupCard 4)) hyAmbient hzAmbient
  cases hright : χ ⟨cup.orderEmbOfFin hcupCard 4, y, z,
      horderY _ (cup.orderEmbOfFin_mem hcupCard 4), hyz⟩ with
  | left => rfl
  | right =>
      simp [TurnSequenceAllowed, hbridgeY, hbridgeZ, hleft, hright] at hallowed

/-- Every ambient vertex outside a strong `k`-set has a local four-index
obstruction when the ambient set contains no strong `(k+1)`-set. -/
theorem strong_extension_failure_of_no_strong_succ
    {n k : ℕ} {χ : TripleColoring n}
    {ambient polygon : Finset (Fin n)} {q : Fin n}
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = k)
    (hpolygon : IsStrongPolygonSet χ polygon)
    (hqAmbient : q ∈ ambient) (hqPolygon : q ∉ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient (k + 1)) :
    HasStrongExtensionFailure χ polygon q := by
  classical
  by_contra hfailure
  have hstrongInsert : IsStrongPolygonSet χ (insert q polygon) := by
    intro i j k l hij hjk hkl hi hj hk hl
    by_cases hq : i = q ∨ j = q ∨ k = q ∨ l = q
    · by_contra hbad
      exact hfailure ⟨i, j, k, l, hij, hjk, hkl,
        hi, hj, hk, hl, hq, hbad⟩
    · apply hpolygon hij hjk hkl
      · rcases Finset.mem_insert.mp hi with hi | hi
        · exact (hq (Or.inl hi)).elim
        · exact hi
      · rcases Finset.mem_insert.mp hj with hj | hj
        · exact (hq (Or.inr (Or.inl hj))).elim
        · exact hj
      · rcases Finset.mem_insert.mp hk with hk | hk
        · exact (hq (Or.inr (Or.inr (Or.inl hk)))).elim
        · exact hk
      · rcases Finset.mem_insert.mp hl with hl | hl
        · exact (hq (Or.inr (Or.inr (Or.inr hl)))).elim
        · exact hl
  apply hnoStrong
  refine ⟨insert q polygon, ?_, ?_, hstrongInsert⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · exact hpolygonSub hx
  · rw [Finset.card_insert_of_notMem hqPolygon, hpolygonCard]

/-- The residual `4+5` witness with every unused vertex equipped with its
one-vertex nonextension certificate. This is the interface for the remaining
finite signature count; it does not itself assert that the count closes. -/
theorem two_cap_free_sides_contains_charged_capFour_or_strongSix
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hleftCard : 7 ≤ left.card) (hrightCard : 7 ≤ right.card)
    (htotal : 22 ≤ left.card + right.card)
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    (∃ cap : Finset (Fin n), cap ⊆ left ∪ right ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ (cap ∩ left).Nonempty ∧ (cap ∩ right).Nonempty ∧
      ∀ q ∈ left ∪ right, q ∉ cap → HasCapExtensionFailure χ cap q) ∨
    (∃ polygon : Finset (Fin n), polygon ⊆ left ∪ right ∧
      polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧
      ∀ q ∈ left ∪ right, q ∉ polygon →
        HasStrongExtensionFailure χ polygon q) := by
  rcases two_cap_free_sides_contains_crossing_capFour_or_strongSix
      hdisjoint horder hone hleftCap hrightCap hleftCard hrightCard
      htotal hnoCup with hcap | hstrong
  · obtain ⟨cap, hcapSub, hcapCard, hcapSet, hleftMeet, hrightMeet⟩ := hcap
    refine Or.inl ⟨cap, hcapSub, hcapCard, hcapSet,
      hleftMeet, hrightMeet, ?_⟩
    intro q hqUnion hqCap
    exact cap_extension_failure_of_no_cap_succ hcapSub hcapCard hcapSet
      hqUnion hqCap hnoCap
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonSet⟩ := hstrong
    refine Or.inr ⟨polygon, hpolygonSub, hpolygonCard, hpolygonSet, ?_⟩
    intro q hqUnion hqPolygon
    exact strong_extension_failure_of_no_strong_succ
      hpolygonSub hpolygonCard hpolygonSet hqUnion hqPolygon hnoStrong

/-- Residual form of the local gate after the ordinary cup--cap bounds have
been discharged.  Only side sizes from seven through fifteen remain. -/
def TwoCapFreeSidesCore567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      left.card + right.card ≤ 21

/-- Exact hereditary 22-vertex form of the two-side gate.  This is the finite
forcing statement tested by the bounded SAT family. -/
def TwoCapFreeSidesForce567AtTwentyTwo : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      left.card + right.card = 22 →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 5 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 7

/-- The exact 22-vertex forcing statement implies the residual cardinality
window theorem by hereditary restriction. -/
theorem twoCapFreeSidesCore567_of_forceAtTwentyTwo
    (hforce : TwoCapFreeSidesForce567AtTwentyTwo) :
    TwoCapFreeSidesCore567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hleftSeven hleftFifteen _hrightSeven _hrightFifteen
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 22 ≤ left.card + right.card := by omega
  have hneeded : 22 - left.card ≤ right.card := by omega
  obtain ⟨right', hrightSub, hrightCard⟩ :=
    Finset.exists_subset_card_eq hneeded
  have htotal : left.card + right'.card = 22 := by omega
  have hdisjoint' : Disjoint left right' := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    exact (Finset.disjoint_left.mp hdisjoint) hxLeft (hrightSub hxRight)
  have horder' : ∀ x ∈ left, ∀ y ∈ right', x < y := by
    intro x hx y hy
    exact horder x hx y (hrightSub hy)
  have hunionSub : left ∪ right' ⊆ left ∪ right := by
    exact Finset.union_subset_union_right hrightSub
  have hrightCap' : ¬ContainsCapSet χ right' 4 := by
    intro hcap
    exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
  have hone' : OneChangeOn χ (left ∪ right') := hone.mono hunionSub
  rcases hforce hdisjoint' horder' htotal hleftCap hrightCap' hone' with
      hcap | hcup | hstrong
  · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
  · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)

/-- The residual cardinality-window theorem is sufficient for the complete
two-side bound. -/
theorem twoCapFreeSidesBound567_of_core
    (hcore : TwoCapFreeSidesCore567) : TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  have hbound := hcore hdisjoint horder hleftCap hrightCap hone
    hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
    hnoCap hnoCup hnoStrong
  omega

/-- Combined reduction: it is enough to prove the exact hereditary
22-vertex forcing proposition. -/
theorem twoCapFreeSidesBound567_of_forceAtTwentyTwo
    (hforce : TwoCapFreeSidesForce567AtTwentyTwo) :
    TwoCapFreeSidesBound567 :=
  twoCapFreeSidesBound567_of_core
    (twoCapFreeSidesCore567_of_forceAtTwentyTwo hforce)

end ErdosSzekeres
