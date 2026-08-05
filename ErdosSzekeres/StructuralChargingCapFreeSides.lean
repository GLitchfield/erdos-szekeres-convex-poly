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

/-- A vertex strictly before a four-cap has a forced left-turn obstruction
through the first two cap vertices when ambient five-caps are forbidden. -/
theorem capFour_forces_left_bridge_before_of_no_capFive
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient)
    (horder : ∀ x ∈ cap, q < x) (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨q, cap.orderEmbOfFin hcapCard 0, cap.orderEmbOfFin hcapCard 1,
      horder _ (cap.orderEmbOfFin_mem hcapCard 0),
      (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![q, ce 0, ce 1, ce 2, ce 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact horder _ (cap.orderEmbOfFin_mem hcapCard _))
  have hfmem : ∀ i : Fin 5, f i ∈ ambient := by
    intro i
    fin_cases i <;>
      simp [f, ce, hqAmbient,
        hcapSub (cap.orderEmbOfFin_mem hcapCard _)]
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfmem i
  cases hfirst : χ ⟨q, cap.orderEmbOfFin hcapCard 0,
      cap.orderEmbOfFin hcapCard 1,
      horder _ (cap.orderEmbOfFin_mem hcapCard 0),
      (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ with
  | left => rfl
  | right =>
    exfalso
    apply hnoCap
    refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · apply FinsetPolygon.IsCap.image
      apply isMonochromaticChain_finFive_of_consecutive f (hone.mono hfsub)
      · simpa [f, ce] using hfirst
      · simpa [f, ce] using hcap _
          (cap.orderEmbOfFin_mem hcapCard 0)
          (cap.orderEmbOfFin_mem hcapCard 1)
          (cap.orderEmbOfFin_mem hcapCard 2)
      · simpa [f, ce] using hcap _
          (cap.orderEmbOfFin_mem hcapCard 1)
          (cap.orderEmbOfFin_mem hcapCard 2)
          (cap.orderEmbOfFin_mem hcapCard 3)

/-- A vertex strictly after a four-cap has a forced left-turn obstruction
through the last two cap vertices when ambient five-caps are forbidden. -/
theorem capFour_forces_left_bridge_after_of_no_capFive
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient)
    (horder : ∀ x ∈ cap, x < q) (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨cap.orderEmbOfFin hcapCard 2, cap.orderEmbOfFin hcapCard 3, q,
      (cap.orderEmbOfFin hcapCard).strictMono (by decide),
      horder _ (cap.orderEmbOfFin_mem hcapCard 3)⟩ = Turn.left := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![ce 0, ce 1, ce 2, ce 3, q] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact horder _ (cap.orderEmbOfFin_mem hcapCard _))
  have hfmem : ∀ i : Fin 5, f i ∈ ambient := by
    intro i
    fin_cases i <;>
      simp [f, ce, hqAmbient,
        hcapSub (cap.orderEmbOfFin_mem hcapCard _)]
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfmem i
  cases hlast : χ ⟨cap.orderEmbOfFin hcapCard 2,
      cap.orderEmbOfFin hcapCard 3, q,
      (cap.orderEmbOfFin hcapCard).strictMono (by decide),
      horder _ (cap.orderEmbOfFin_mem hcapCard 3)⟩ with
  | left => rfl
  | right =>
    exfalso
    apply hnoCap
    refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · simpa using Finset.card_image_of_injective Finset.univ f.injective
    · apply FinsetPolygon.IsCap.image
      apply isMonochromaticChain_finFive_of_consecutive f (hone.mono hfsub)
      · simpa [f, ce] using hcap _
          (cap.orderEmbOfFin_mem hcapCard 0)
          (cap.orderEmbOfFin_mem hcapCard 1)
          (cap.orderEmbOfFin_mem hcapCard 2)
      · simpa [f, ce] using hcap _
          (cap.orderEmbOfFin_mem hcapCard 1)
          (cap.orderEmbOfFin_mem hcapCard 2)
          (cap.orderEmbOfFin_mem hcapCard 3)
      · simpa [f, ce] using hlast

/-- Every increasing five-chain in a one-change set avoiding five-caps has a
left turn among its three consecutive triples. -/
theorem finFive_has_left_consecutive_of_oneChange_no_capFive
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)}
    (f : Fin 5 ↪o Fin n) (hfsub : Finset.univ.image f ⊆ ambient)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.left ∨
      χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.left ∨
      χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = Turn.left := by
  cases h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ with
  | left => exact Or.inl rfl
  | right =>
    cases h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ with
    | left => exact Or.inr (Or.inl rfl)
    | right =>
      cases h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ with
      | left => exact Or.inr (Or.inr rfl)
      | right =>
        exfalso
        apply hnoCap
        refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
        · simpa using Finset.card_image_of_injective Finset.univ f.injective
        · apply FinsetPolygon.IsCap.image
          exact isMonochromaticChain_finFive_of_consecutive f
            (hone.mono hfsub) h012 h123 h234

/-- In the first interior gap of a four-cap, one of the two consecutive
triples containing the inserted vertex must turn left. -/
theorem capFour_gap_one_has_two_failure_signatures
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient)
    (hlower : cap.orderEmbOfFin hcapCard 0 < q)
    (hupper : q < cap.orderEmbOfFin hcapCard 1)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨cap.orderEmbOfFin hcapCard 0, q,
        cap.orderEmbOfFin hcapCard 1, hlower, hupper⟩ = Turn.left ∨
      χ ⟨q, cap.orderEmbOfFin hcapCard 1,
        cap.orderEmbOfFin hcapCard 2, hupper,
        (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  have hq (j : Fin 4) (hj : (1 : Fin 4) ≤ j) : q < ce j :=
    hupper.trans_le (ce.monotone hj)
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![ce 0, q, ce 1, ce 2, ce 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact hlower
        | exact hq _ (by decide))
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [f, ce, hqAmbient,
        hcapSub (cap.orderEmbOfFin_mem hcapCard _)]
  rcases finFive_has_left_consecutive_of_oneChange_no_capFive
      f hfsub hone hnoCap with hfirst | hsecond | hthird
  · exact Or.inl (by simpa [f, ce] using hfirst)
  · exact Or.inr (by simpa [f, ce] using hsecond)
  · have hright := hcap ⟨ce 1, ce 2, ce 3, by simp, by simp⟩
      (cap.orderEmbOfFin_mem hcapCard 1)
      (cap.orderEmbOfFin_mem hcapCard 2)
      (cap.orderEmbOfFin_mem hcapCard 3)
    rw [show χ ⟨ce 1, ce 2, ce 3, by simp, by simp⟩ = Turn.left by
      simpa [f, ce] using hthird] at hright
    exact Turn.noConfusion hright

/-- In the middle gap of a four-cap, at least one of the three consecutive
triples containing the inserted vertex must turn left. -/
theorem capFour_gap_two_has_three_failure_signatures
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hqAmbient : q ∈ ambient)
    (hlower : cap.orderEmbOfFin hcapCard 1 < q)
    (hupper : q < cap.orderEmbOfFin hcapCard 2)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨cap.orderEmbOfFin hcapCard 0,
        cap.orderEmbOfFin hcapCard 1, q,
        (cap.orderEmbOfFin hcapCard).strictMono (by decide), hlower⟩ =
      Turn.left ∨
    χ ⟨cap.orderEmbOfFin hcapCard 1, q,
        cap.orderEmbOfFin hcapCard 2, hlower, hupper⟩ = Turn.left ∨
    χ ⟨q, cap.orderEmbOfFin hcapCard 2,
        cap.orderEmbOfFin hcapCard 3, hupper,
        (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  have hcq (i : Fin 4) (hi : i ≤ (1 : Fin 4)) : ce i < q :=
    (ce.monotone hi).trans_lt hlower
  have hqc (j : Fin 4) (hj : (2 : Fin 4) ≤ j) : q < ce j :=
    hupper.trans_le (ce.monotone hj)
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![ce 0, ce 1, q, ce 2, ce 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact hcq _ (by decide)
        | exact hqc _ (by decide))
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [f, ce, hqAmbient,
        hcapSub (cap.orderEmbOfFin_mem hcapCard _)]
  simpa [f, ce] using
    (finFive_has_left_consecutive_of_oneChange_no_capFive
      f hfsub hone hnoCap)

/-- In the third interior gap of a four-cap, one of the two consecutive
triples containing the inserted vertex must turn left. -/
theorem capFour_gap_three_has_two_failure_signatures
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient)
    (hlower : cap.orderEmbOfFin hcapCard 2 < q)
    (hupper : q < cap.orderEmbOfFin hcapCard 3)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    χ ⟨cap.orderEmbOfFin hcapCard 1,
        cap.orderEmbOfFin hcapCard 2, q,
        (cap.orderEmbOfFin hcapCard).strictMono (by decide), hlower⟩ =
      Turn.left ∨
    χ ⟨cap.orderEmbOfFin hcapCard 2, q,
        cap.orderEmbOfFin hcapCard 3, hlower, hupper⟩ = Turn.left := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  have hcq (i : Fin 4) (hi : i ≤ (2 : Fin 4)) : ce i < q :=
    (ce.monotone hi).trans_lt hlower
  let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![ce 0, ce 1, ce 2, q, ce 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact hcq _ (by decide)
        | exact hupper)
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [f, ce, hqAmbient,
        hcapSub (cap.orderEmbOfFin_mem hcapCard _)]
  rcases finFive_has_left_consecutive_of_oneChange_no_capFive
      f hfsub hone hnoCap with hfirst | hsecond | hthird
  · have hright := hcap ⟨ce 0, ce 1, ce 2, by simp, by simp⟩
      (cap.orderEmbOfFin_mem hcapCard 0)
      (cap.orderEmbOfFin_mem hcapCard 1)
      (cap.orderEmbOfFin_mem hcapCard 2)
    rw [show χ ⟨ce 0, ce 1, ce 2, by simp, by simp⟩ = Turn.left by
      simpa [f, ce] using hfirst] at hright
    exact Turn.noConfusion hright
  · exact Or.inl (by simpa [f, ce] using hsecond)
  · exact Or.inr (by simpa [f, ce] using hthird)

/-- The nine possible consecutive failure locations obtained by inserting a
vertex into one of the five gaps around a sorted four-cap. -/
inductive CapFourFailureSignature where
  | before
  | gapOneFirst
  | gapOneSecond
  | gapTwoFirst
  | gapTwoMiddle
  | gapTwoThird
  | gapThreeFirst
  | gapThreeSecond
  | after
  deriving DecidableEq, Fintype

/-- A vertex realizes a named failure signature when it lies in the
corresponding gap and the indicated consecutive triple turns left. -/
def RealizesCapFourFailureSignature {n : ℕ} (χ : TripleColoring n)
    (cap : Finset (Fin n)) (hcapCard : cap.card = 4) (q : Fin n) :
    CapFourFailureSignature → Prop
  | .before =>
      ∃ hq0 : q < cap.orderEmbOfFin hcapCard 0,
        χ ⟨q, cap.orderEmbOfFin hcapCard 0,
          cap.orderEmbOfFin hcapCard 1, hq0,
          (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left
  | .gapOneFirst =>
      ∃ h0q : cap.orderEmbOfFin hcapCard 0 < q,
        ∃ hq1 : q < cap.orderEmbOfFin hcapCard 1,
          χ ⟨cap.orderEmbOfFin hcapCard 0, q,
            cap.orderEmbOfFin hcapCard 1, h0q, hq1⟩ = Turn.left
  | .gapOneSecond =>
      ∃ h0q : cap.orderEmbOfFin hcapCard 0 < q,
        ∃ hq1 : q < cap.orderEmbOfFin hcapCard 1,
          χ ⟨q, cap.orderEmbOfFin hcapCard 1,
            cap.orderEmbOfFin hcapCard 2, hq1,
            (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left
  | .gapTwoFirst =>
      ∃ h1q : cap.orderEmbOfFin hcapCard 1 < q,
        ∃ hq2 : q < cap.orderEmbOfFin hcapCard 2,
          χ ⟨cap.orderEmbOfFin hcapCard 0,
            cap.orderEmbOfFin hcapCard 1, q,
            (cap.orderEmbOfFin hcapCard).strictMono (by decide), h1q⟩ = Turn.left
  | .gapTwoMiddle =>
      ∃ h1q : cap.orderEmbOfFin hcapCard 1 < q,
        ∃ hq2 : q < cap.orderEmbOfFin hcapCard 2,
          χ ⟨cap.orderEmbOfFin hcapCard 1, q,
            cap.orderEmbOfFin hcapCard 2, h1q, hq2⟩ = Turn.left
  | .gapTwoThird =>
      ∃ h1q : cap.orderEmbOfFin hcapCard 1 < q,
        ∃ hq2 : q < cap.orderEmbOfFin hcapCard 2,
          χ ⟨q, cap.orderEmbOfFin hcapCard 2,
            cap.orderEmbOfFin hcapCard 3, hq2,
            (cap.orderEmbOfFin hcapCard).strictMono (by decide)⟩ = Turn.left
  | .gapThreeFirst =>
      ∃ h2q : cap.orderEmbOfFin hcapCard 2 < q,
        ∃ hq3 : q < cap.orderEmbOfFin hcapCard 3,
          χ ⟨cap.orderEmbOfFin hcapCard 1,
            cap.orderEmbOfFin hcapCard 2, q,
            (cap.orderEmbOfFin hcapCard).strictMono (by decide), h2q⟩ = Turn.left
  | .gapThreeSecond =>
      ∃ h2q : cap.orderEmbOfFin hcapCard 2 < q,
        ∃ hq3 : q < cap.orderEmbOfFin hcapCard 3,
          χ ⟨cap.orderEmbOfFin hcapCard 2, q,
            cap.orderEmbOfFin hcapCard 3, h2q, hq3⟩ = Turn.left
  | .after =>
      ∃ h3q : cap.orderEmbOfFin hcapCard 3 < q,
        χ ⟨cap.orderEmbOfFin hcapCard 2,
          cap.orderEmbOfFin hcapCard 3, q,
          (cap.orderEmbOfFin hcapCard).strictMono (by decide), h3q⟩ = Turn.left

/-- There are exactly nine named four-cap insertion signatures. -/
theorem card_capFourFailureSignature :
    Fintype.card CapFourFailureSignature = 9 := by
  decide

/-- Every vertex outside a four-cap realizes one of the nine exact failure
signatures when the ambient set obeys the one-change law and has no five-cap. -/
theorem capFour_realizes_some_failure_signature
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)} {q : Fin n}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hqAmbient : q ∈ ambient) (hqCap : q ∉ cap)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    ∃ signature : CapFourFailureSignature,
      RealizesCapFourFailureSignature χ cap hcapCard q signature := by
  let ce : Fin 4 ↪o Fin n := cap.orderEmbOfFin hcapCard
  have hqne (i : Fin 4) : q ≠ ce i := by
    intro hqi
    apply hqCap
    rw [hqi]
    exact cap.orderEmbOfFin_mem hcapCard i
  by_cases hq0 : q < ce 0
  · have hbefore : ∀ x ∈ cap, q < x := by
      intro x hx
      rw [← Finset.image_orderEmbOfFin_univ cap hcapCard] at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hq0.trans_le (ce.monotone (Fin.zero_le i))
    exact ⟨.before, hq0,
      capFour_forces_left_bridge_before_of_no_capFive
        hcapSub hcapCard hcap hqAmbient hbefore hone hnoCap⟩
  have h0q : ce 0 < q :=
    lt_of_le_of_ne (le_of_not_gt hq0) (Ne.symm (hqne 0))
  by_cases hq1 : q < ce 1
  · rcases capFour_gap_one_has_two_failure_signatures
        hcapSub hcapCard hcap hqAmbient h0q hq1 hone hnoCap with hfirst | hsecond
    · exact ⟨.gapOneFirst, h0q, hq1, hfirst⟩
    · exact ⟨.gapOneSecond, h0q, hq1, hsecond⟩
  have h1q : ce 1 < q :=
    lt_of_le_of_ne (le_of_not_gt hq1) (Ne.symm (hqne 1))
  by_cases hq2 : q < ce 2
  · rcases capFour_gap_two_has_three_failure_signatures
        hcapSub hcapCard hqAmbient h1q hq2 hone hnoCap with
      hfirst | hmiddle | hthird
    · exact ⟨.gapTwoFirst, h1q, hq2, hfirst⟩
    · exact ⟨.gapTwoMiddle, h1q, hq2, hmiddle⟩
    · exact ⟨.gapTwoThird, h1q, hq2, hthird⟩
  have h2q : ce 2 < q :=
    lt_of_le_of_ne (le_of_not_gt hq2) (Ne.symm (hqne 2))
  by_cases hq3 : q < ce 3
  · rcases capFour_gap_three_has_two_failure_signatures
        hcapSub hcapCard hcap hqAmbient h2q hq3 hone hnoCap with hfirst | hsecond
    · exact ⟨.gapThreeFirst, h2q, hq3, hfirst⟩
    · exact ⟨.gapThreeSecond, h2q, hq3, hsecond⟩
  have h3q : ce 3 < q :=
    lt_of_le_of_ne (le_of_not_gt hq3) (Ne.symm (hqne 3))
  have hafter : ∀ x ∈ cap, x < q := by
    intro x hx
    rw [← Finset.image_orderEmbOfFin_univ cap hcapCard] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (ce.monotone (Fin.le_last i)).trans_lt h3q
  exact ⟨.after, h3q,
    capFour_forces_left_bridge_after_of_no_capFive
      hcapSub hcapCard hcap hqAmbient hafter hone hnoCap⟩

/-- A total assignment of outside vertices to realized four-cap failure
signatures. Only its values on `ambient \ cap` are constrained. -/
def IsCapFourFailureCharge {n : ℕ} (χ : TripleColoring n)
    (ambient cap : Finset (Fin n)) (hcapCard : cap.card = 4)
    (charge : Fin n → CapFourFailureSignature) : Prop :=
  ∀ q ∈ ambient, q ∉ cap →
    RealizesCapFourFailureSignature χ cap hcapCard q (charge q)

/-- The outside vertices assigned a specified four-cap failure signature. -/
def capFourFailureFiber {n : ℕ} (ambient cap : Finset (Fin n))
    (charge : Fin n → CapFourFailureSignature)
    (signature : CapFourFailureSignature) : Finset (Fin n) :=
  (ambient \ cap).filter fun q ↦ charge q = signature

/-- The exact nine-signature localization admits a total failure charge. -/
theorem exists_capFourFailureCharge
    {n : ℕ} {χ : TripleColoring n}
    {ambient cap : Finset (Fin n)}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    ∃ charge : Fin n → CapFourFailureSignature,
      IsCapFourFailureCharge χ ambient cap hcapCard charge := by
  classical
  have hexists (q : Fin n) :
      ∃ signature : CapFourFailureSignature,
        q ∈ ambient → q ∉ cap →
          RealizesCapFourFailureSignature χ cap hcapCard q signature := by
    by_cases hqAmbient : q ∈ ambient
    · by_cases hqCap : q ∈ cap
      · exact ⟨.before, fun _ hqNotCap ↦ (hqNotCap hqCap).elim⟩
      · obtain ⟨signature, hsignature⟩ :=
          capFour_realizes_some_failure_signature hcapSub hcapCard hcap
            hqAmbient hqCap hone hnoCap
        exact ⟨signature, fun _ _ ↦ hsignature⟩
    · exact ⟨.before, fun hq _ ↦ (hqAmbient hq).elim⟩
  choose charge hcharge using hexists
  exact ⟨charge, fun q hqAmbient hqCap ↦
    hcharge q hqAmbient hqCap⟩

/-- Nine fibers of capacity two, with one strict fiber, contain at most
seventeen elements. -/
theorem card_le_seventeen_of_capFourFailure_fibers
    {n : ℕ} (outside : Finset (Fin n))
    (charge : Fin n → CapFourFailureSignature)
    (hcapacity : ∀ signature,
      (outside.filter fun q ↦ charge q = signature).card ≤ 2)
    (strictSignature : CapFourFailureSignature)
    (hstrict : (outside.filter fun q ↦
      charge q = strictSignature).card ≤ 1) :
    outside.card ≤ 17 := by
  have hpartition : outside.card =
      ∑ signature : CapFourFailureSignature,
        (outside.filter fun q ↦ charge q = signature).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  have htarget :
      (∑ signature : CapFourFailureSignature,
        if signature = strictSignature then 1 else 2) = 17 := by
    fin_cases strictSignature <;> decide
  rw [hpartition]
  calc
    (∑ signature : CapFourFailureSignature,
        (outside.filter fun q ↦ charge q = signature).card) ≤
        ∑ signature : CapFourFailureSignature,
          if signature = strictSignature then 1 else 2 := by
      apply Finset.sum_le_sum
      intro signature _
      by_cases hsignature : signature = strictSignature
      · subst signature
        simpa using hstrict
      · simpa [hsignature] using hcapacity signature
    _ = 17 := htarget

/-- A sharp nine-signature charge bounds the whole ambient set by 21 once
the selected cap has four vertices. -/
theorem ambient_card_le_twenty_one_of_sharp_capFourFailure_charge
    {n : ℕ} {ambient cap : Finset (Fin n)}
    (hcapSub : cap ⊆ ambient) (hcapCard : cap.card = 4)
    (charge : Fin n → CapFourFailureSignature)
    (hcapacity : ∀ signature,
      (capFourFailureFiber ambient cap charge signature).card ≤ 2)
    (strictSignature : CapFourFailureSignature)
    (hstrict : (capFourFailureFiber ambient cap charge strictSignature).card ≤ 1) :
    ambient.card ≤ 21 := by
  have houtside : (ambient \ cap).card ≤ 17 :=
    card_le_seventeen_of_capFourFailure_fibers
      (ambient \ cap) charge hcapacity strictSignature hstrict
  have hcard := Finset.card_sdiff_add_card_eq_card hcapSub
  omega

/-- If a four-cap meets the left side of an ordered cut, a vertex on the
right side realizes one of the eight signatures other than `before`. -/
theorem capFour_right_vertex_realizes_nonbefore_signature
    {n : ℕ} {χ : TripleColoring n}
    {left right cap : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hcapSub : cap ⊆ left ∪ right) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hcapLeft : (cap ∩ left).Nonempty)
    (hqRight : q ∈ right) (hqCap : q ∉ cap)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 5) :
    ∃ signature : CapFourFailureSignature,
      signature ≠ .before ∧
        RealizesCapFourFailureSignature χ cap hcapCard q signature := by
  obtain ⟨signature, hsignature⟩ :=
    capFour_realizes_some_failure_signature hcapSub hcapCard hcap
      (Finset.mem_union_right left hqRight) hqCap hone hnoCap
  refine ⟨signature, ?_, hsignature⟩
  intro heq
  subst signature
  rcases hsignature with ⟨hqFirst, _⟩
  obtain ⟨x, hx⟩ := hcapLeft
  have hxCap := (Finset.mem_inter.mp hx).1
  have hxLeft := (Finset.mem_inter.mp hx).2
  have hfirstLe : cap.orderEmbOfFin hcapCard 0 ≤ x := by
    rw [← Finset.image_orderEmbOfFin_univ cap hcapCard] at hxCap
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxCap
    obtain ⟨i, rfl⟩ := hxCap
    exact (cap.orderEmbOfFin hcapCard).monotone (Fin.zero_le i)
  exact (hqFirst.trans_le hfirstLe).asymm (horder x hxLeft q hqRight)

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

/-- Two cross-turn probes suffice to promote a five-cup and a later vertex to
a strong six-set.  The remaining cross turns are forced by the one-change
law and the right bridge supplied by six-cup avoidance. -/
theorem cupFive_containsStrongSix_of_outer_right_inner_left
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (horder : ∀ x ∈ cup, x < y) (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (houter : χ ⟨cup.orderEmbOfFin hcupCard 0,
      cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ = Turn.right)
    (hinner : χ ⟨cup.orderEmbOfFin hcupCard 2,
      cup.orderEmbOfFin hcupCard 3, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ = Turn.left) :
    ContainsStrongPolygonSet χ ambient 6 := by
  let ce : Fin 5 ↪o Fin n := cup.orderEmbOfFin hcupCard
  have cmem (i : Fin 5) : ce i ∈ cup :=
    cup.orderEmbOfFin_mem hcupCard i
  have hc (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
      χ ⟨ce i, ce j, ce k, ce.strictMono hij, ce.strictMono hjk⟩ =
        Turn.left := hcup _ (cmem i) (cmem j) (cmem k)
  have h023 : χ ⟨ce 0, ce 2, ce 3, by simp, by simp⟩ = Turn.left :=
    hcup _ (cmem 0) (cmem 2) (cmem 3)
  have h123 : χ ⟨ce 1, ce 2, ce 3, by simp, by simp⟩ = Turn.left :=
    hcup _ (cmem 1) (cmem 2) (cmem 3)
  have h012 : χ ⟨ce 0, ce 1, ce 2, by simp, by simp⟩ = Turn.left :=
    hcup _ (cmem 0) (cmem 1) (cmem 2)
  have hallow023 := hone
    (ce.strictMono (show (0 : Fin 5) < 2 by decide))
    (ce.strictMono (show (2 : Fin 5) < 3 by decide))
    (horder _ (cmem 3)) (hcupSub (cmem 0)) (hcupSub (cmem 2))
    (hcupSub (cmem 3)) hyAmbient
  have heq023 := hallow023.all_eq_of_outer_eq (h023.trans hinner.symm)
  have h02 : χ ⟨ce 0, ce 2, y, by simp,
      horder _ (cmem 2)⟩ = Turn.left := heq023.1.symm.trans h023
  have h03 : χ ⟨ce 0, ce 3, y, by simp,
      horder _ (cmem 3)⟩ = Turn.left := heq023.2.1.symm.trans h02
  have hallow123 := hone
    (ce.strictMono (show (1 : Fin 5) < 2 by decide))
    (ce.strictMono (show (2 : Fin 5) < 3 by decide))
    (horder _ (cmem 3)) (hcupSub (cmem 1)) (hcupSub (cmem 2))
    (hcupSub (cmem 3)) hyAmbient
  have heq123 := hallow123.all_eq_of_outer_eq (h123.trans hinner.symm)
  have h12 : χ ⟨ce 1, ce 2, y, by simp,
      horder _ (cmem 2)⟩ = Turn.left := heq123.1.symm.trans h123
  have h13 : χ ⟨ce 1, ce 3, y, by simp,
      horder _ (cmem 3)⟩ = Turn.left := heq123.2.1.symm.trans h12
  have hallow012 := hone
    (ce.strictMono (show (0 : Fin 5) < 1 by decide))
    (ce.strictMono (show (1 : Fin 5) < 2 by decide))
    (horder _ (cmem 2)) (hcupSub (cmem 0)) (hcupSub (cmem 1))
    (hcupSub (cmem 2)) hyAmbient
  have heq012 := hallow012.all_eq_of_outer_eq (h012.trans h12.symm)
  have h01 : χ ⟨ce 0, ce 1, y, by simp,
      horder _ (cmem 1)⟩ = Turn.left := heq012.1.symm.trans h012
  have hbridge := cupFive_forces_right_bridge_of_no_cupSix
    hcupSub hcupCard hcup hyAmbient horder hone hnoCup
  have hallow014 := hone
    (ce.strictMono (show (0 : Fin 5) < 1 by decide))
    (ce.strictMono (show (1 : Fin 5) < 4 by decide))
    (horder _ (cmem 4)) (hcupSub (cmem 0)) (hcupSub (cmem 1))
    (hcupSub (cmem 4)) hyAmbient
  have h14 : χ ⟨ce 1, ce 4, y, by simp,
      horder _ (cmem 4)⟩ = Turn.right := by
    have hneq : χ ⟨ce 0, ce 1, ce 4, by simp, by simp⟩ ≠
        χ ⟨ce 0, ce 4, y, by simp, horder _ (cmem 4)⟩ := by
      rw [hc 0 1 4 (by decide) (by decide), houter]
      exact Turn.noConfusion
    exact (hallow014.third_eq_fourth_of_first_ne_third hneq).symm.trans
      houter
  have hallow024 := hone
    (ce.strictMono (show (0 : Fin 5) < 2 by decide))
    (ce.strictMono (show (2 : Fin 5) < 4 by decide))
    (horder _ (cmem 4)) (hcupSub (cmem 0)) (hcupSub (cmem 2))
    (hcupSub (cmem 4)) hyAmbient
  have h24 : χ ⟨ce 2, ce 4, y, by simp,
      horder _ (cmem 4)⟩ = Turn.right := by
    have hneq : χ ⟨ce 0, ce 2, ce 4, by simp, by simp⟩ ≠
        χ ⟨ce 0, ce 4, y, by simp, horder _ (cmem 4)⟩ := by
      rw [hc 0 2 4 (by decide) (by decide), houter]
      exact Turn.noConfusion
    exact (hallow024.third_eq_fourth_of_first_ne_third hneq).symm.trans
      houter
  let f : Fin 6 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![ce 0, ce 1, ce 2, ce 3, ce 4, y] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact ce.strictMono (by decide)
        | exact horder _ (cmem _))
  have hfsub : Finset.univ.image f ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;> simp [f, hyAmbient, hcupSub (cmem _)]
  refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · apply FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image
    rw [isStrongPolygonOn_finSix_iff]
    simp only [StrongSixValues]
    simp [f, ce, hc, h01, h02, h03, houter, h12, h13,
      h14, hinner, h24, hbridge]

/-- The two probe colors of a vertex lying strictly after a selected
five-cup. -/
structure FiveCupProbeState where
  outer : Turn
  inner : Turn
  deriving DecidableEq, Repr

/-- Package the outer and inner five-cup probe colors as a four-state value. -/
def fiveCupProbeState {n : ℕ} (χ : TripleColoring n)
    (cup : Finset (Fin n)) (hcupCard : cup.card = 5) (y : Fin n)
    (horder : ∀ x ∈ cup, x < y) : FiveCupProbeState where
  outer := χ ⟨cup.orderEmbOfFin hcupCard 0,
    cup.orderEmbOfFin hcupCard 4, y,
    (cup.orderEmbOfFin hcupCard).strictMono (by decide),
    horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩
  inner := χ ⟨cup.orderEmbOfFin hcupCard 2,
    cup.orderEmbOfFin hcupCard 3, y,
    (cup.orderEmbOfFin hcupCard).strictMono (by decide),
    horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩

/-- Every later vertex is classified by the two probe colors, unless it
already extends the five-cup to a strong six-set. -/
theorem cupFive_two_probe_trichotomy
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (horder : ∀ x ∈ cup, x < y) (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    χ ⟨cup.orderEmbOfFin hcupCard 0, cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ = Turn.left ∨
    χ ⟨cup.orderEmbOfFin hcupCard 2, cup.orderEmbOfFin hcupCard 3, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ = Turn.right ∨
    ContainsStrongPolygonSet χ ambient 6 := by
  cases houter : χ ⟨cup.orderEmbOfFin hcupCard 0,
      cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ with
  | left => exact Or.inl rfl
  | right =>
    cases hinner : χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ with
    | left =>
        exact Or.inr (Or.inr
          (cupFive_containsStrongSix_of_outer_right_inner_left
            hcupSub hcupCard hcup hyAmbient horder hone hnoCup
            houter hinner))
    | right => exact Or.inr (Or.inl rfl)

/-- If both probe colors change between two later vertices, the new outer
probe color propagates through both extreme cup vertices, while the new inner
probe color propagates through both inner cup vertices. -/
theorem cupFive_probe_transitions_force_four_anchor_colors
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y z : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hyAmbient : y ∈ ambient) (hzAmbient : z ∈ ambient)
    (horderY : ∀ x ∈ cup, x < y) (hyz : y < z)
    (hone : OneChangeOn χ ambient)
    (houter : χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩)
    (hinner : χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩) :
    (χ ⟨cup.orderEmbOfFin hcupCard 0, y, z,
        horderY _ (cup.orderEmbOfFin_mem hcupCard 0), hyz⟩ =
        χ ⟨cup.orderEmbOfFin hcupCard 0,
          cup.orderEmbOfFin hcupCard 4, z,
          (cup.orderEmbOfFin hcupCard).strictMono (by decide),
          (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩ ∧
      χ ⟨cup.orderEmbOfFin hcupCard 4, y, z,
        horderY _ (cup.orderEmbOfFin_mem hcupCard 4), hyz⟩ =
        χ ⟨cup.orderEmbOfFin hcupCard 0,
          cup.orderEmbOfFin hcupCard 4, z,
          (cup.orderEmbOfFin hcupCard).strictMono (by decide),
          (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩) ∧
    (χ ⟨cup.orderEmbOfFin hcupCard 2, y, z,
        horderY _ (cup.orderEmbOfFin_mem hcupCard 2), hyz⟩ =
        χ ⟨cup.orderEmbOfFin hcupCard 2,
          cup.orderEmbOfFin hcupCard 3, z,
          (cup.orderEmbOfFin hcupCard).strictMono (by decide),
          (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩ ∧
      χ ⟨cup.orderEmbOfFin hcupCard 3, y, z,
        horderY _ (cup.orderEmbOfFin_mem hcupCard 3), hyz⟩ =
        χ ⟨cup.orderEmbOfFin hcupCard 2,
          cup.orderEmbOfFin hcupCard 3, z,
          (cup.orderEmbOfFin hcupCard).strictMono (by decide),
          (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩) := by
  constructor
  · exact hone.probe_transition_forces_pair_colors
      ((cup.orderEmbOfFin hcupCard).strictMono (by decide))
      (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)) hyz
      (hcupSub (cup.orderEmbOfFin_mem hcupCard 0))
      (hcupSub (cup.orderEmbOfFin_mem hcupCard 4))
      hyAmbient hzAmbient houter
  · exact hone.probe_transition_forces_pair_colors
      ((cup.orderEmbOfFin hcupCard).strictMono (by decide))
      (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)) hyz
      (hcupSub (cup.orderEmbOfFin_mem hcupCard 2))
      (hcupSub (cup.orderEmbOfFin_mem hcupCard 3))
      hyAmbient hzAmbient hinner

/-- Consequently, if the ambient set has no strong six-set, every later
vertex has one of two explicit obstruction colors relative to the five-cup. -/
theorem cupFive_outer_left_or_inner_right_of_no_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (horder : ∀ x ∈ cup, x < y) (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 6) :
    χ ⟨cup.orderEmbOfFin hcupCard 0, cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ = Turn.left ∨
    χ ⟨cup.orderEmbOfFin hcupCard 2, cup.orderEmbOfFin hcupCard 3, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ = Turn.right := by
  cases houter : χ ⟨cup.orderEmbOfFin hcupCard 0,
      cup.orderEmbOfFin hcupCard 4, y,
      (cup.orderEmbOfFin hcupCard).strictMono (by decide),
      horder _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ with
  | left => exact Or.inl rfl
  | right =>
    cases hinner : χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horder _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ with
    | left =>
        exact (hnoStrong
          (cupFive_containsStrongSix_of_outer_right_inner_left
            hcupSub hcupCard hcup hyAmbient horder hone hnoCup
            houter hinner)).elim
    | right => exact Or.inr rfl

/-- In the no-strong-six branch, only three of the four two-probe states can
occur: outer-left or inner-right. -/
theorem fiveCupProbeState_admissible_of_no_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup) (hyAmbient : y ∈ ambient)
    (horder : ∀ x ∈ cup, x < y) (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 6) :
    (fiveCupProbeState χ cup hcupCard y horder).outer = Turn.left ∨
      (fiveCupProbeState χ cup hcupCard y horder).inner = Turn.right := by
  simpa [fiveCupProbeState] using
    cupFive_outer_left_or_inner_right_of_no_strongSix
      hcupSub hcupCard hcup hyAmbient horder hone hnoCup hnoStrong

/-- One of the two same-middle triples uses a designated vertex. -/
def MiddleComparisonUses {n : ℕ} (q i i' j k k' : Fin n) : Prop :=
  i = q ∨ i' = q ∨ j = q ∨ k = q ∨ k' = q

/-- A same-middle disagreement obtained by adjoining one vertex to a
middle-determined set. The failed comparison explicitly uses that vertex. -/
def HasMiddleExtensionFailure {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q polygon ∧
      i' ∈ insert q polygon ∧
      j ∈ insert q polygon ∧
      k ∈ insert q polygon ∧
      k' ∈ insert q polygon ∧
      MiddleComparisonUses q i i' j k k' ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- The three order-theoretic roles in which an adjoined vertex can occur in
a failed same-middle comparison. -/
inductive MiddleExtensionFailureRole where
  | leftEndpoint
  | middle
  | rightEndpoint
  deriving DecidableEq, Repr

/-- A role records whether the fresh vertex is a left endpoint, the shared
middle, or a right endpoint of the failed comparison. -/
def MiddleExtensionFailureRole.Matches {n : ℕ}
    (role : MiddleExtensionFailureRole) (q i i' j k k' : Fin n) : Prop :=
  match role with
  | .leftEndpoint => i = q ∨ i' = q
  | .middle => j = q
  | .rightEndpoint => k = q ∨ k' = q

/-- Witness-level role refinement of `HasMiddleExtensionFailure`. -/
def HasMiddleExtensionFailureWithRole {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n)
    (role : MiddleExtensionFailureRole) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q polygon ∧
      i' ∈ insert q polygon ∧
      j ∈ insert q polygon ∧
      k ∈ insert q polygon ∧
      k' ∈ insert q polygon ∧
      role.Matches q i i' j k k' ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- Every middle-extension failure occupies at least one of the three
order-theoretic roles. -/
theorem hasMiddleExtensionFailure_iff_exists_role
    {n : ℕ} {χ : TripleColoring n}
    {polygon : Finset (Fin n)} {q : Fin n} :
    HasMiddleExtensionFailure χ polygon q ↔
      ∃ role, HasMiddleExtensionFailureWithRole χ polygon q role := by
  constructor
  · rintro ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
      hi, hi', hj, hk, hk', huses, hneq⟩
    rcases huses with hiq | hiq | hjq | hkq | hk'q
    · exact ⟨.leftEndpoint, i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', Or.inl hiq, hneq⟩
    · exact ⟨.leftEndpoint, i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', Or.inr hiq, hneq⟩
    · exact ⟨.middle, i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', hjq, hneq⟩
    · exact ⟨.rightEndpoint, i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', Or.inl hkq, hneq⟩
    · exact ⟨.rightEndpoint, i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', Or.inr hk'q, hneq⟩
  · rintro ⟨role, i, i', j, k, k', hij, hi'j, hjk, hjk',
      hi, hi', hj, hk, hk', hrole, hneq⟩
    refine ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
      hi, hi', hj, hk, hk', ?_, hneq⟩
    cases role with
    | leftEndpoint =>
        rcases hrole with hiq | hiq
        · exact Or.inl hiq
        · exact Or.inr (Or.inl hiq)
    | middle => exact Or.inr (Or.inr (Or.inl hrole))
    | rightEndpoint =>
        rcases hrole with hkq | hkq
        · exact Or.inr (Or.inr (Or.inr (Or.inl hkq)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hkq)))

/-- A fresh vertex before every polygon vertex can only participate as a left
endpoint of a failed same-middle comparison. -/
theorem middleExtensionFailure_role_left_of_before
    {n : ℕ} {χ : TripleColoring n}
    {polygon : Finset (Fin n)} {q : Fin n}
    (hbefore : ∀ x ∈ polygon, q < x)
    (hfailure : HasMiddleExtensionFailure χ polygon q) :
    HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint := by
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', huses, hneq⟩ := hfailure
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  have hleft : i = q ∨ i' = q := by
    rcases huses with hiq | hiq | hjq | hkq | hk'q
    · exact Or.inl hiq
    · exact Or.inr hiq
    · have hiq : i ≠ q := by omega
      have hiPolygon := memPolygon hi hiq
      have hqi := hbefore i hiPolygon
      omega
    · have hjq : j ≠ q := by omega
      have hjPolygon := memPolygon hj hjq
      have hqj := hbefore j hjPolygon
      omega
    · have hjq : j ≠ q := by omega
      have hjPolygon := memPolygon hj hjq
      have hqj := hbefore j hjPolygon
      omega
  exact ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hleft, hneq⟩

/-- A fresh vertex after every polygon vertex can only participate as a right
endpoint of a failed same-middle comparison. -/
theorem middleExtensionFailure_role_right_of_after
    {n : ℕ} {χ : TripleColoring n}
    {polygon : Finset (Fin n)} {q : Fin n}
    (hafter : ∀ x ∈ polygon, x < q)
    (hfailure : HasMiddleExtensionFailure χ polygon q) :
    HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint := by
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', huses, hneq⟩ := hfailure
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  have hright : k = q ∨ k' = q := by
    rcases huses with hiq | hiq | hjq | hkq | hk'q
    · have hjq : j ≠ q := by omega
      have hjPolygon := memPolygon hj hjq
      have hjq' := hafter j hjPolygon
      omega
    · have hjq : j ≠ q := by omega
      have hjPolygon := memPolygon hj hjq
      have hjq' := hafter j hjPolygon
      omega
    · have hkq : k ≠ q := by omega
      have hkPolygon := memPolygon hk hkq
      have hkq' := hafter k hkPolygon
      omega
    · exact Or.inl hkq
    · exact Or.inr hk'q
  exact ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hright, hneq⟩

/-- If a middle-determined `a`-set cannot absorb one fresh ambient vertex
without creating a forbidden strong `(a+1)`-set, a failed same-middle
comparison explicitly uses the fresh vertex. -/
theorem middle_extension_failure_of_no_strong_succ
    {n a : ℕ} {χ : TripleColoring n}
    {ambient polygon : Finset (Fin n)} {q : Fin n}
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = a)
    (hpolygon : IsMiddleDeterminedOn χ polygon)
    (hqAmbient : q ∈ ambient) (hqPolygon : q ∉ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient (a + 1)) :
    HasMiddleExtensionFailure χ polygon q := by
  classical
  by_contra hfailure
  have mem_without_q {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  have hmiddle : IsMiddleDeterminedOn χ (insert q polygon) := by
    intro i i' j k k' hij hi'j hjk hjk' hi hi' hj hk hk'
    by_cases hq : MiddleComparisonUses q i i' j k k'
    · by_contra hneq
      exact hfailure ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', hq, hneq⟩
    · simp only [MiddleComparisonUses, not_or] at hq
      exact hpolygon hij hi'j hjk hjk'
        (mem_without_q hi hq.1)
        (mem_without_q hi' hq.2.1)
        (mem_without_q hj hq.2.2.1)
        (mem_without_q hk hq.2.2.2.1)
        (mem_without_q hk' hq.2.2.2.2)
  apply hnoStrong
  refine ⟨insert q polygon, ?_, ?_,
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mpr hmiddle⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · exact hpolygonSub hx
  · rw [Finset.card_insert_of_notMem hqPolygon, hpolygonCard]

/-- Every outside vertex of a strong six-set carries a same-middle extension
failure when the ambient set avoids strong seven-sets. -/
theorem strongSix_middle_extension_failure_of_no_strongSeven
    {n : ℕ} {χ : TripleColoring n}
    {ambient polygon : Finset (Fin n)} {q : Fin n}
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = 6)
    (hpolygon : IsStrongPolygonSet χ polygon)
    (hqAmbient : q ∈ ambient) (hqPolygon : q ∉ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    HasMiddleExtensionFailure χ polygon q := by
  apply middle_extension_failure_of_no_strong_succ
    hpolygonSub hpolygonCard
    (FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hpolygon)
    hqAmbient hqPolygon
  simpa using hnoStrong

/-- A same-middle color disagreement obtained by adjoining a pair of vertices
to a middle-determined set.  At least one vertex in the two compared triples
must lie outside the original set. -/
def HasMiddlePairExtensionFailure {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q r : Fin n) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q (insert r polygon) ∧
      i' ∈ insert q (insert r polygon) ∧
      j ∈ insert q (insert r polygon) ∧
      k ∈ insert q (insert r polygon) ∧
      k' ∈ insert q (insert r polygon) ∧
      (i ∉ polygon ∨ i' ∉ polygon ∨ j ∉ polygon ∨
        k ∉ polygon ∨ k' ∉ polygon) ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- If a middle-determined `a`-set does not extend to a strong `(a+2)`-set
with two fresh ambient vertices, a same-middle disagreement uses at least one
of the fresh vertices. -/
theorem middle_pair_extension_failure_of_no_strong_add_two
    {n a : ℕ} {χ : TripleColoring n}
    {ambient polygon : Finset (Fin n)} {q r : Fin n}
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = a)
    (hpolygon : IsMiddleDeterminedOn χ polygon)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqPolygon : q ∉ polygon) (hrPolygon : r ∉ polygon) (hqr : q ≠ r)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient (a + 2)) :
    HasMiddlePairExtensionFailure χ polygon q r := by
  classical
  by_contra hfailure
  have hmiddle : IsMiddleDeterminedOn χ (insert q (insert r polygon)) := by
    intro i i' j k k' hij hi'j hjk hjk' hi hi' hj hk hk'
    by_cases hout : i ∉ polygon ∨ i' ∉ polygon ∨ j ∉ polygon ∨
        k ∉ polygon ∨ k' ∉ polygon
    · by_contra hneq
      exact hfailure ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
        hi, hi', hj, hk, hk', hout, hneq⟩
    · push Not at hout
      exact hpolygon hij hi'j hjk hjk'
        hout.1 hout.2.1 hout.2.2.1 hout.2.2.2.1 hout.2.2.2.2
  apply hnoStrong
  refine ⟨insert q (insert r polygon), ?_, ?_,
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mpr hmiddle⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hqAmbient
    · exact hrAmbient
    · exact hpolygonSub hx
  · have hqInsert : q ∉ insert r polygon := by
      simp [hqPolygon, hqr]
    rw [Finset.card_insert_of_notMem hqInsert,
      Finset.card_insert_of_notMem hrPolygon, hpolygonCard]

/-- A same-middle disagreement that genuinely couples both newly adjoined
vertices. -/
def HasCoupledMiddlePairFailure {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q r : Fin n) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q (insert r polygon) ∧
      i' ∈ insert q (insert r polygon) ∧
      j ∈ insert q (insert r polygon) ∧
      k ∈ insert q (insert r polygon) ∧
      k' ∈ insert q (insert r polygon) ∧
      MiddleComparisonUses q i i' j k k' ∧
      MiddleComparisonUses r i i' j k k' ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- If two vertices separately preserve middle determinacy but cannot jointly
extend to a strong polygon, some failed comparison must use both vertices. -/
theorem coupled_middle_pair_failure_of_no_strong_add_two
    {n a : ℕ} {χ : TripleColoring n}
    {ambient polygon : Finset (Fin n)} {q r : Fin n}
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = a)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqPolygon : q ∉ polygon) (hrPolygon : r ∉ polygon) (hqr : q ≠ r)
    (hmiddleQ : IsMiddleDeterminedOn χ (insert q polygon))
    (hmiddleR : IsMiddleDeterminedOn χ (insert r polygon))
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient (a + 2)) :
    HasCoupledMiddlePairFailure χ polygon q r := by
  classical
  by_contra hfailure
  have mem_without_r {x : Fin n} (hx : x ∈ insert q (insert r polygon))
      (hxr : x ≠ r) : x ∈ insert q polygon := by
    simp only [Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inl rfl
    · exact (hxr rfl).elim
    · exact Or.inr hx
  have mem_without_q {x : Fin n} (hx : x ∈ insert q (insert r polygon))
      (hxq : x ≠ q) : x ∈ insert r polygon := by
    simp only [Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact (hxq rfl).elim
    · exact Or.inl rfl
    · exact Or.inr hx
  have hmiddle : IsMiddleDeterminedOn χ (insert q (insert r polygon)) := by
    intro i i' j k k' hij hi'j hjk hjk' hi hi' hj hk hk'
    by_cases hq : MiddleComparisonUses q i i' j k k'
    · by_cases hr : MiddleComparisonUses r i i' j k k'
      · by_contra hneq
        exact hfailure ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
          hi, hi', hj, hk, hk', hq, hr, hneq⟩
      · simp only [MiddleComparisonUses, not_or] at hr
        exact hmiddleQ hij hi'j hjk hjk'
          (mem_without_r hi hr.1)
          (mem_without_r hi' hr.2.1)
          (mem_without_r hj hr.2.2.1)
          (mem_without_r hk hr.2.2.2.1)
          (mem_without_r hk' hr.2.2.2.2)
    · simp only [MiddleComparisonUses, not_or] at hq
      exact hmiddleR hij hi'j hjk hjk'
        (mem_without_q hi hq.1)
        (mem_without_q hi' hq.2.1)
        (mem_without_q hj hq.2.2.1)
        (mem_without_q hk hq.2.2.2.1)
        (mem_without_q hk' hq.2.2.2.2)
  apply hnoStrong
  refine ⟨insert q (insert r polygon), ?_, ?_,
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mpr hmiddle⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hqAmbient
    · exact hrAmbient
    · exact hpolygonSub hx
  · have hqInsert : q ∉ insert r polygon := by
      simp [hqPolygon, hqr]
    rw [Finset.card_insert_of_notMem hqInsert,
      Finset.card_insert_of_notMem hrPolygon, hpolygonCard]

/-- Every pair outside a five-cup carries a genuine pairwise middle-color
obstruction when the ambient set avoids strong seven-sets. -/
theorem cupFive_middle_pair_failure_of_no_strongSeven
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {q r : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hcup : IsCupSet χ cup)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqCup : q ∉ cup) (hrCup : r ∉ cup) (hqr : q ≠ r)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    HasMiddlePairExtensionFailure χ cup q r := by
  apply middle_pair_extension_failure_of_no_strong_add_two
      hcupSub hcupCard
      (FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp
        (FinsetPolygon.IsCupSet.isStrongPolygonSet hcup))
      hqAmbient hrAmbient hqCup hrCup hqr
  simpa using hnoStrong

/-- When both probes change to different new colors, their propagated anchor
colors give an explicit coupled middle disagreement at the earlier outside
vertex. -/
theorem cupFive_probe_transitions_give_coupled_middle_failure
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y z : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hyAmbient : y ∈ ambient) (hzAmbient : z ∈ ambient)
    (horderY : ∀ x ∈ cup, x < y) (hyz : y < z)
    (hone : OneChangeOn χ ambient)
    (houter : χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩)
    (hinner : χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩)
    (hnew : χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩) :
    HasCoupledMiddlePairFailure χ cup y z := by
  have htrans := cupFive_probe_transitions_force_four_anchor_colors
    hcupSub hcupCard hyAmbient hzAmbient horderY hyz hone houter hinner
  have hneq : χ ⟨cup.orderEmbOfFin hcupCard 0, y, z,
      horderY _ (cup.orderEmbOfFin_mem hcupCard 0), hyz⟩ ≠
      χ ⟨cup.orderEmbOfFin hcupCard 2, y, z,
        horderY _ (cup.orderEmbOfFin_mem hcupCard 2), hyz⟩ := by
    intro heq
    exact hnew (htrans.1.1.symm.trans (heq.trans htrans.2.1))
  refine ⟨cup.orderEmbOfFin hcupCard 0,
    cup.orderEmbOfFin hcupCard 2, y, z, z,
    horderY _ (cup.orderEmbOfFin_mem hcupCard 0),
    horderY _ (cup.orderEmbOfFin_mem hcupCard 2), hyz, hyz,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hneq⟩
  all_goals simp [MiddleComparisonUses,
    cup.orderEmbOfFin_mem hcupCard]

/-- Every adjacent pair of five-cup probe states has an unchanged probe, has
equal new probe colors, or produces an explicit coupled middle failure. This
is the exhaustive transition split needed by the signature count. -/
theorem fiveCupProbeState_transition_partition
    {n : ℕ} {χ : TripleColoring n}
    {ambient cup : Finset (Fin n)} {y z : Fin n}
    (hcupSub : cup ⊆ ambient) (hcupCard : cup.card = 5)
    (hyAmbient : y ∈ ambient) (hzAmbient : z ∈ ambient)
    (horderY : ∀ x ∈ cup, x < y) (hyz : y < z)
    (hone : OneChangeOn χ ambient) :
    let stateY := fiveCupProbeState χ cup hcupCard y horderY
    let stateZ := fiveCupProbeState χ cup hcupCard z
      (fun x hx ↦ (horderY x hx).trans hyz)
    stateY.outer = stateZ.outer ∨
      stateY.inner = stateZ.inner ∨
      stateZ.outer = stateZ.inner ∨
      HasCoupledMiddlePairFailure χ cup y z := by
  dsimp only [fiveCupProbeState]
  by_cases houter :
      χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 4)⟩ =
      χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩
  · exact Or.inl houter
  by_cases hinner :
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, y,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        horderY _ (cup.orderEmbOfFin_mem hcupCard 3)⟩ =
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩
  · exact Or.inr (Or.inl hinner)
  by_cases hnew :
      χ ⟨cup.orderEmbOfFin hcupCard 0,
        cup.orderEmbOfFin hcupCard 4, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 4)).trans hyz⟩ =
      χ ⟨cup.orderEmbOfFin hcupCard 2,
        cup.orderEmbOfFin hcupCard 3, z,
        (cup.orderEmbOfFin hcupCard).strictMono (by decide),
        (horderY _ (cup.orderEmbOfFin_mem hcupCard 3)).trans hyz⟩
  · exact Or.inr (Or.inr (Or.inl hnew))
  · exact Or.inr (Or.inr (Or.inr
      (cupFive_probe_transitions_give_coupled_middle_failure
        hcupSub hcupCard hyAmbient hzAmbient horderY hyz hone
        houter hinner hnew)))

/-- On an ordered cut, two right-side vertices receive non-`before` cap
signatures, while their five-cup probe states obey the exhaustive transition
partition. This is the common local interface for the multiplicity count. -/
theorem right_pair_has_cap_signatures_and_probe_transition
    {n : ℕ} {χ : TripleColoring n}
    {left right cup cap : Finset (Fin n)} {y z : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hcupSub : cup ⊆ left) (hcupCard : cup.card = 5)
    (hcapSub : cap ⊆ left ∪ right) (hcapCard : cap.card = 4)
    (hcap : IsCapSet χ cap) (hcapLeft : (cap ∩ left).Nonempty)
    (hyRight : y ∈ right) (hzRight : z ∈ right) (hyz : y < z)
    (hyCap : y ∉ cap) (hzCap : z ∉ cap)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 5) :
    ∃ signatureY signatureZ : CapFourFailureSignature,
      signatureY ≠ .before ∧ signatureZ ≠ .before ∧
      RealizesCapFourFailureSignature χ cap hcapCard y signatureY ∧
      RealizesCapFourFailureSignature χ cap hcapCard z signatureZ ∧
      (let horderY : ∀ x ∈ cup, x < y :=
          fun x hx ↦ horder x (hcupSub hx) y hyRight
        let stateY := fiveCupProbeState χ cup hcupCard y horderY
        let stateZ := fiveCupProbeState χ cup hcupCard z
          (fun x hx ↦ (horderY x hx).trans hyz)
        stateY.outer = stateZ.outer ∨
          stateY.inner = stateZ.inner ∨
          stateZ.outer = stateZ.inner ∨
          HasCoupledMiddlePairFailure χ cup y z) := by
  obtain ⟨signatureY, hsignatureY, hrealizesY⟩ :=
    capFour_right_vertex_realizes_nonbefore_signature horder hcapSub
      hcapCard hcap hcapLeft hyRight hyCap hone hnoCap
  obtain ⟨signatureZ, hsignatureZ, hrealizesZ⟩ :=
    capFour_right_vertex_realizes_nonbefore_signature horder hcapSub
      hcapCard hcap hcapLeft hzRight hzCap hone hnoCap
  refine ⟨signatureY, signatureZ, hsignatureY, hsignatureZ,
    hrealizesY, hrealizesZ, ?_⟩
  exact fiveCupProbeState_transition_partition
    (hcupSub.trans Finset.subset_union_left) hcupCard
    (Finset.mem_union_right left hyRight)
    (Finset.mem_union_right left hzRight)
    (fun x hx ↦ horder x (hcupSub hx) y hyRight) hyz hone

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

/-- The remaining sharp charging contract. In every hypothetical 22-vertex
counterexample, one can select a four-cap and a realized nine-signature charge
whose fibers have capacity two, with at least one nonsaturated fiber. -/
def TwoCapFreeSidesSharpCapCharge567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      left.card + right.card = 22 →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      ∃ (cap : Finset (Fin n)) (hcapCard : cap.card = 4)
          (charge : Fin n → CapFourFailureSignature)
          (strictSignature : CapFourFailureSignature),
        cap ⊆ left ∪ right ∧ IsCapSet χ cap ∧
          IsCapFourFailureCharge χ (left ∪ right) cap hcapCard charge ∧
          (∀ signature,
            (capFourFailureFiber (left ∪ right) cap charge signature).card ≤ 2) ∧
          (capFourFailureFiber (left ∪ right) cap charge strictSignature).card ≤ 1

/-- The sharp charging contract closes the exact 22-vertex forcing theorem. -/
theorem twoCapFreeSidesForce567AtTwentyTwo_of_sharpCapCharge
    (hcharge : TwoCapFreeSidesSharpCapCharge567) :
    TwoCapFreeSidesForce567AtTwentyTwo := by
  intro n χ left right hdisjoint horder htotal hleftCap hrightCap hone
  by_contra htarget
  have hnoCap : ¬ContainsCapSet χ (left ∪ right) 5 :=
    fun hcap ↦ htarget (Or.inl hcap)
  have hnoCup : ¬ContainsCupSet χ (left ∪ right) 6 :=
    fun hcup ↦ htarget (Or.inr (Or.inl hcup))
  have hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7 :=
    fun hstrong ↦ htarget (Or.inr (Or.inr hstrong))
  obtain ⟨cap, hcapCard, charge, strictSignature, hcapSub, _hcap,
      _hrealizes, hcapacity, hstrict⟩ :=
    hcharge hdisjoint horder htotal hleftCap hrightCap hone
      hnoCap hnoCup hnoStrong
  have hbound : (left ∪ right).card ≤ 21 :=
    ambient_card_le_twenty_one_of_sharp_capFourFailure_charge
      hcapSub hcapCard charge hcapacity strictSignature hstrict
  have hunionCard : (left ∪ right).card = 22 := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    exact htotal
  omega

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

/-- The single sharp charging contract is sufficient for the complete local
`(5,6,7)` two-side bound. -/
theorem twoCapFreeSidesBound567_of_sharpCapCharge
    (hcharge : TwoCapFreeSidesSharpCapCharge567) :
    TwoCapFreeSidesBound567 :=
  twoCapFreeSidesBound567_of_forceAtTwentyTwo
    (twoCapFreeSidesForce567AtTwentyTwo_of_sharpCapCharge hcharge)

end ErdosSzekeres
