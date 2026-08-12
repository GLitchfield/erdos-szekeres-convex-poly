module

public import ErdosSzekeres.StructuralChargingCarrierOnlyRectangleProfiles567

@[expose] public section

/-!
# The mixed carrier-only omission normal form at state 567

This file classifies the carrier-only omission systems having four area-five
rectangles and two area-eight rectangles.  The argument is color-free after
the witness normalization supplied by the rectangle system.
-/

namespace ErdosSzekeres

/-- The explicit normal form in which the area-eight rectangles have two rows
and four columns. -/
def IsShortFirstMixedOmissionNormalForm567 {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) : Prop :=
  ∃ p q c d : Fin n, ∃ P Q A₀ A₁ B₀ B₁ D₀ D₁ : Finset (Fin n),
    p ∈ first ∧ q ∈ first ∧ c ∈ second ∧ d ∈ second ∧
    p ≠ q ∧ c ≠ d ∧ P.card = 2 ∧ Q.card = 2 ∧ Disjoint P Q ∧
    P ∪ Q = (first.erase p).erase q ∧
    witnesses = {A₀, A₁, B₀, B₁, D₀, D₁} ∧
    ({A₀, A₁, B₀, B₁, D₀, D₁} :
      Finset (Finset (Fin n))).card = 6 ∧
    first \ A₀ = first.erase p ∧ second \ A₀ = {c} ∧
    first \ A₁ = first.erase q ∧ second \ A₁ = {d} ∧
    first \ B₀ = {p} ∧ second \ B₀ = second.erase d ∧
    first \ B₁ = {q} ∧ second \ B₁ = second.erase c ∧
    first \ D₀ = P ∧ second \ D₀ = (second.erase c).erase d ∧
    first \ D₁ = Q ∧ second \ D₁ = (second.erase c).erase d

/-- The transposed normal form, in which the area-eight rectangles have four
rows and two columns. -/
def IsShortSecondMixedOmissionNormalForm567 {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) : Prop :=
  IsShortFirstMixedOmissionNormalForm567 second first witnesses

private theorem add_eq_six_of_mul_eq_five {a b : ℕ} (h : a * b = 5) :
    a + b = 6 := by
  have haPos : 0 < a := by
    by_contra ha
    have : a = 0 := by omega
    simp [this] at h
  have hbPos : 0 < b := by
    by_contra hb
    have : b = 0 := by omega
    simp [this] at h
  have haLe : a ≤ 5 := Nat.le_of_dvd (by norm_num) ⟨b, h.symm⟩
  have hbDvd : b ∣ 5 := ⟨a, by simpa [Nat.mul_comm] using h.symm⟩
  have hbLe : b ≤ 5 := Nat.le_of_dvd (by norm_num) hbDvd
  interval_cases a <;> interval_cases b <;> omega

/-- The mixed counts themselves force both carrier universes to have six
vertices; no carrier-cardinality premise is required by the normal form. -/
theorem IsCarrierOnlyOmissionRectangleSystem567.carrier_cards_eq_six_of_mixed
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem :
      IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfive : OmissionAreaCount567 first second witnesses 5 = 4)
    (height : OmissionAreaCount567 first second witnesses 8 = 2) :
    first.card = 6 ∧ second.card = 6 := by
  classical
  let row : Finset (Fin n) → Finset (Fin n) := fun third ↦ first \ third
  let col : Finset (Fin n) → Finset (Fin n) := fun third ↦ second \ third
  let rect : Finset (Fin n) → Finset (Fin n × Fin n) :=
    fun third ↦ (row third).product (col third)
  let f5 := witnesses.filter fun third ↦ (row third).card * (col third).card = 5
  let f8 := witnesses.filter fun third ↦ (row third).card * (col third).card = 8
  have hf5Card : f5.card = 4 := by
    simpa [f5, row, col, OmissionAreaCount567] using hfive
  have hf8Card : f8.card = 2 := by
    simpa [f8, row, col, OmissionAreaCount567] using height
  obtain ⟨third, hthird5⟩ : f5.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hthirdData := Finset.mem_filter.mp hthird5
  rcases hsystem.1 third hthirdData.1 with
    ⟨_hthirdCard, _hstrong, _hsub, _htwo, hfirstPos, hfirstLe,
      hsecondPos, hsecondLe, hcarrierSum, _hprofile⟩
  have hrowCard : (row third).card =
      first.card - (third ∩ first).card := by
    simp [row, Finset.card_sdiff]
  have hcolCard : (col third).card =
      second.card - (third ∩ second).card := by
    simp [col, Finset.card_sdiff]
  have hsideSum : (row third).card + (col third).card = 6 :=
    add_eq_six_of_mul_eq_five hthirdData.2
  have hcarrierCardSum : first.card + second.card = 12 := by
    rw [hrowCard, hcolCard] at hsideSum
    have hfirstInterLe : (third ∩ first).card ≤ first.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsecondInterLe : (third ∩ second).card ≤ second.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  have hf58 : Disjoint f5 f8 := by
    apply Finset.disjoint_left.mpr
    intro candidate hc5 hc8
    have h5 := (Finset.mem_filter.mp hc5).2
    have h8 := (Finset.mem_filter.mp hc8).2
    omega
  have hpairwise :
      ((f5 ∪ f8 : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint rect := by
    intro third₁ hthird₁ third₂ hthird₂ hne
    have hmem₁ : third₁ ∈ witnesses := by
      rcases Finset.mem_union.mp hthird₁ with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    have hmem₂ : third₂ ∈ witnesses := by
      rcases Finset.mem_union.mp hthird₂ with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    simpa [rect, row, col, CarrierOnlyOmissionRectangle567] using
      hsystem.2.2 third₁ hmem₁ third₂ hmem₂ hne
  have hselectedCard : ((f5 ∪ f8).biUnion rect).card = 36 := by
    rw [Finset.card_biUnion hpairwise, Finset.sum_union hf58]
    have hsum5 : (∑ third ∈ f5, (rect third).card) = f5.card * 5 := by
      calc
        (∑ third ∈ f5, (rect third).card) = ∑ _third ∈ f5, 5 := by
          apply Finset.sum_congr rfl
          intro candidate hc
          simpa [rect, Finset.card_product] using
            (Finset.mem_filter.mp hc).2
        _ = f5.card * 5 := by simp
    have hsum8 : (∑ third ∈ f8, (rect third).card) = f8.card * 8 := by
      calc
        (∑ third ∈ f8, (rect third).card) = ∑ _third ∈ f8, 8 := by
          apply Finset.sum_congr rfl
          intro candidate hc
          simpa [rect, Finset.card_product] using
            (Finset.mem_filter.mp hc).2
        _ = f8.card * 8 := by simp
    rw [hsum5, hsum8, hf5Card, hf8Card]
  have hselectedSub : (f5 ∪ f8).biUnion rect ⊆ first.product second := by
    intro pair hpair
    obtain ⟨third, _hthird, hpairThird⟩ := Finset.mem_biUnion.mp hpair
    have hdata := Finset.mem_product.mp hpairThird
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_sdiff.mp hdata.1).1,
        (Finset.mem_sdiff.mp hdata.2).1⟩
  have hproductLower : 36 ≤ first.card * second.card := by
    have hle := Finset.card_le_card hselectedSub
    simpa [hselectedCard, Finset.card_product] using hle
  have hfirstLe : first.card ≤ 12 := by omega
  have hsecondLe : second.card ≤ 12 := by omega
  interval_cases hfirstCard : first.card <;>
    interval_cases hsecondCard : second.card <;> omega


end ErdosSzekeres

end
