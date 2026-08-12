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

private theorem mixed_local_incidence_table {a b c d : ℕ}
    (ha : a ≤ 4) (hb : b ≤ 4) (hc : c ≤ 2) (hd : d ≤ 2)
    (hweighted : a + 5 * b + 2 * c + 4 * d = 6) :
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨
      (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨
      (a = 2 ∧ b = 0 ∧ c = 2 ∧ d = 0) ∨
      (a = 4 ∧ b = 0 ∧ c = 1 ∧ d = 0) := by
  interval_cases a <;> interval_cases b <;>
    interval_cases c <;> interval_cases d <;> omega

private theorem aggregate_mixed_local_incidence_table
    {α : Type*} [DecidableEq α] (carrier : Finset α)
    (a b c d : α → ℕ)
    (htable : ∀ x ∈ carrier,
      (a x = 0 ∧ b x = 0 ∧ c x = 1 ∧ d x = 1) ∨
        (a x = 1 ∧ b x = 1 ∧ c x = 0 ∧ d x = 0) ∨
        (a x = 2 ∧ b x = 0 ∧ c x = 0 ∧ d x = 1) ∨
        (a x = 2 ∧ b x = 0 ∧ c x = 2 ∧ d x = 0) ∨
        (a x = 4 ∧ b x = 0 ∧ c x = 1 ∧ d x = 0)) :
    ∃ n₀ n₁ n₂ n₃ n₄ : ℕ,
      carrier.card = n₀ + n₁ + n₂ + n₃ + n₄ ∧
      (∑ x ∈ carrier, a x) = n₁ + 2 * n₂ + 2 * n₃ + 4 * n₄ ∧
      (∑ x ∈ carrier, b x) = n₁ ∧
      (∑ x ∈ carrier, c x) = n₀ + 2 * n₃ + n₄ ∧
      (∑ x ∈ carrier, d x) = n₀ + n₂ := by
  classical
  induction carrier using Finset.induction_on with
  | empty =>
      exact ⟨0, 0, 0, 0, 0, by simp⟩
  | @insert x carrier hx ih =>
      have htableCarrier : ∀ y ∈ carrier,
          (a y = 0 ∧ b y = 0 ∧ c y = 1 ∧ d y = 1) ∨
            (a y = 1 ∧ b y = 1 ∧ c y = 0 ∧ d y = 0) ∨
            (a y = 2 ∧ b y = 0 ∧ c y = 0 ∧ d y = 1) ∨
            (a y = 2 ∧ b y = 0 ∧ c y = 2 ∧ d y = 0) ∨
            (a y = 4 ∧ b y = 0 ∧ c y = 1 ∧ d y = 0) := by
        intro y hy
        exact htable y (Finset.mem_insert_of_mem hy)
      obtain ⟨n₀, n₁, n₂, n₃, n₄,
        hcard, haSum, hbSum, hcSum, hdSum⟩ := ih htableCarrier
      have hxType := htable x (Finset.mem_insert_self x carrier)
      rcases hxType with hxType | hxType | hxType | hxType | hxType
      · exact ⟨n₀ + 1, n₁, n₂, n₃, n₄, by
          simp [hx] at *
          omega⟩
      · exact ⟨n₀, n₁ + 1, n₂, n₃, n₄, by
          simp [hx] at *
          omega⟩
      · exact ⟨n₀, n₁, n₂ + 1, n₃, n₄, by
          simp [hx] at *
          omega⟩
      · exact ⟨n₀, n₁, n₂, n₃ + 1, n₄, by
          simp [hx] at *
          omega⟩
      · exact ⟨n₀, n₁, n₂, n₃, n₄ + 1, by
          simp [hx] at *
          omega⟩

private theorem sum_membership_counts
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (carrier : Finset α) (family : Finset ι) (side : ι → Finset α)
    (hsub : ∀ i ∈ family, side i ⊆ carrier) :
    (∑ x ∈ carrier, (family.filter fun i ↦ x ∈ side i).card) =
      ∑ i ∈ family, (side i).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact and_iff_right_of_imp (fun hx ↦ hsub i hi hx)

private theorem rectangle_partition_row_incidence_sum
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (rows : Finset α) (cols : Finset β) (family : Finset ι)
    (row : ι → Finset α) (col : ι → Finset β)
    (hrowSub : ∀ i, row i ⊆ rows) (hcolSub : ∀ i, col i ⊆ cols)
    (hcover : ∀ x ∈ rows, ∀ y ∈ cols, ∃ i ∈ family,
      x ∈ row i ∧ y ∈ col i)
    (hdisjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (row i) (row j) ∨ Disjoint (col i) (col j))
    (x : α) (hx : x ∈ rows) :
    (∑ i ∈ family, if x ∈ row i then (col i).card else 0) = cols.card := by
  classical
  let active := family.filter fun i ↦ x ∈ row i
  have hunion : active.biUnion col = cols := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, _hi, hyCol⟩ := Finset.mem_biUnion.mp hy
      exact hcolSub i hyCol
    · intro hy
      obtain ⟨i, hi, hxRow, hyCol⟩ := hcover x hx y hy
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hxRow⟩, hyCol⟩
  have hpairwise : (active : Set ι).PairwiseDisjoint col := by
    intro i hi j hj hij
    have hiData := Finset.mem_filter.mp hi
    have hjData := Finset.mem_filter.mp hj
    rcases hdisjoint i hiData.1 j hjData.1 hij with hrows | hcols
    · exact (Finset.disjoint_left.mp hrows hiData.2 hjData.2).elim
    · exact hcols
  have hcard := Finset.card_biUnion hpairwise
  rw [hunion] at hcard
  simpa [active, Finset.sum_filter] using hcard.symm

private theorem sum_ite_const_on_family
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (family : Finset ι) (side : ι → Finset α) (x : α)
    (k : ℕ) :
    (∑ i ∈ family, if x ∈ side i then k else 0) =
      (family.filter fun i ↦ x ∈ side i).card * k := by
  classical
  rw [Finset.card_filter]
  simp [Finset.sum_ite]

private theorem not_disjoint_of_card_lt_add_of_subset_mixed
    {α : Type*} [DecidableEq α] {ambient left right : Finset α}
    (hleft : left ⊆ ambient) (hright : right ⊆ ambient)
    (hcard : ambient.card < left.card + right.card) :
    ¬Disjoint left right := by
  intro hdisjoint
  have hunionSub : left ∪ right ⊆ ambient :=
    Finset.union_subset hleft hright
  have hunionCard : (left ∪ right).card = left.card + right.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hle := Finset.card_le_card hunionSub
  omega

private theorem opposite_eight_orientations_impossible
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (rows : Finset α) (cols : Finset β) (family : Finset ι)
    (row : ι → Finset α) (col : ι → Finset β)
    {tallFive wideFive tallEight wideEight : ι}
    (hrowsCard : rows.card = 6) (hcolsCard : cols.card = 6)
    (hrowSub : ∀ i, row i ⊆ rows) (hcolSub : ∀ i, col i ⊆ cols)
    (hdisjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (row i) (row j) ∨ Disjoint (col i) (col j))
    (htallFiveMem : tallFive ∈ family)
    (hwideFiveMem : wideFive ∈ family)
    (htallEightMem : tallEight ∈ family)
    (hwideEightMem : wideEight ∈ family)
    (htallFiveShape : (row tallFive).card = 5 ∧ (col tallFive).card = 1)
    (hwideFiveShape : (row wideFive).card = 1 ∧ (col wideFive).card = 5)
    (htallEightShape : (row tallEight).card = 4 ∧ (col tallEight).card = 2)
    (hwideEightShape : (row wideEight).card = 2 ∧ (col wideEight).card = 4) :
    False := by
  have hneTallWideEight : tallEight ≠ wideEight := by
    intro h
    subst wideEight
    omega
  rcases hdisjoint tallEight htallEightMem wideEight hwideEightMem
      hneTallWideEight with hrows | hcols
  · have hrowUnionSub : row tallEight ∪ row wideEight ⊆ rows :=
      Finset.union_subset (hrowSub tallEight) (hrowSub wideEight)
    have hrowUnionCard : (row tallEight ∪ row wideEight).card = 6 := by
      rw [Finset.card_union_of_disjoint hrows,
        htallEightShape.1, hwideEightShape.1]
    have hrowUnion : row tallEight ∪ row wideEight = rows :=
      Finset.eq_of_subset_of_card_le hrowUnionSub (by
        rw [hrowUnionCard, hrowsCard])
    have hwideNeTallEight : wideFive ≠ tallEight := by
      intro h
      subst tallEight
      omega
    have hwideNeWideEight : wideFive ≠ wideEight := by
      intro h
      subst wideEight
      omega
    have hwideRowsTall : Disjoint (row wideFive) (row tallEight) := by
      rcases hdisjoint wideFive hwideFiveMem tallEight htallEightMem
          hwideNeTallEight with hrow | hcol
      · exact hrow
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          (hcolSub wideFive) (hcolSub tallEight) (by
            rw [hcolsCard, hwideFiveShape.2, htallEightShape.2]
            omega) hcol).elim
    have hwideRowsWide : Disjoint (row wideFive) (row wideEight) := by
      rcases hdisjoint wideFive hwideFiveMem wideEight hwideEightMem
          hwideNeWideEight with hrow | hcol
      · exact hrow
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          (hcolSub wideFive) (hcolSub wideEight) (by
            rw [hcolsCard, hwideFiveShape.2, hwideEightShape.2]
            omega) hcol).elim
    have hwideRowsUnion :
        Disjoint (row wideFive) (row tallEight ∪ row wideEight) :=
      Finset.disjoint_union_right.mpr ⟨hwideRowsTall, hwideRowsWide⟩
    rw [hrowUnion] at hwideRowsUnion
    exact (not_disjoint_of_card_lt_add_of_subset_mixed
      (hrowSub wideFive) (fun _ h ↦ h) (by
        rw [hrowsCard, hwideFiveShape.1]
        omega) hwideRowsUnion).elim
  · have hcolUnionSub : col tallEight ∪ col wideEight ⊆ cols :=
      Finset.union_subset (hcolSub tallEight) (hcolSub wideEight)
    have hcolUnionCard : (col tallEight ∪ col wideEight).card = 6 := by
      rw [Finset.card_union_of_disjoint hcols,
        htallEightShape.2, hwideEightShape.2]
    have hcolUnion : col tallEight ∪ col wideEight = cols :=
      Finset.eq_of_subset_of_card_le hcolUnionSub (by
        rw [hcolUnionCard, hcolsCard])
    have htallNeTallEight : tallFive ≠ tallEight := by
      intro h
      subst tallEight
      omega
    have htallNeWideEight : tallFive ≠ wideEight := by
      intro h
      subst wideEight
      omega
    have htallColsTall : Disjoint (col tallFive) (col tallEight) := by
      rcases hdisjoint tallFive htallFiveMem tallEight htallEightMem
          htallNeTallEight with hrow | hcol
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          (hrowSub tallFive) (hrowSub tallEight) (by
            rw [hrowsCard, htallFiveShape.1, htallEightShape.1]
            omega) hrow).elim
      · exact hcol
    have htallColsWide : Disjoint (col tallFive) (col wideEight) := by
      rcases hdisjoint tallFive htallFiveMem wideEight hwideEightMem
          htallNeWideEight with hrow | hcol
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          (hrowSub tallFive) (hrowSub wideEight) (by
            rw [hrowsCard, htallFiveShape.1, hwideEightShape.1]
            omega) hrow).elim
      · exact hcol
    have htallColsUnion :
        Disjoint (col tallFive) (col tallEight ∪ col wideEight) :=
      Finset.disjoint_union_right.mpr ⟨htallColsTall, htallColsWide⟩
    rw [hcolUnion] at htallColsUnion
    exact (not_disjoint_of_card_lt_add_of_subset_mixed
      (hcolSub tallFive) (fun _ h ↦ h) (by
        rw [hcolsCard, htallFiveShape.2]
        omega) htallColsUnion).elim

private theorem mixed_orientation_arithmetic
    {tf wf te we r₀ r₁ r₂ r₃ r₄ s₀ s₁ s₂ s₃ s₄ : ℕ}
    (hfive : tf + wf = 4) (height : te + we = 2)
    (hrCard : 6 = r₀ + r₁ + r₂ + r₃ + r₄)
    (hra : r₁ + 2 * r₂ + 2 * r₃ + 4 * r₄ = 5 * tf)
    (hrb : r₁ = wf) (hrc : r₀ + 2 * r₃ + r₄ = 4 * te)
    (hrd : r₀ + r₂ = 2 * we)
    (hsCard : 6 = s₀ + s₁ + s₂ + s₃ + s₄)
    (hsa : s₁ + 2 * s₂ + 2 * s₃ + 4 * s₄ = 5 * wf)
    (hsb : s₁ = tf) (hsc : s₀ + 2 * s₃ + s₄ = 4 * we)
    (hsd : s₀ + s₂ = 2 * te) :
    (tf = 1 ∧ wf = 3 ∧ te = 1 ∧ we = 1) ∨
      (tf = 2 ∧ wf = 2 ∧ te = 0 ∧ we = 2) ∨
      (tf = 2 ∧ wf = 2 ∧ te = 1 ∧ we = 1) ∨
      (tf = 2 ∧ wf = 2 ∧ te = 2 ∧ we = 0) ∨
      (tf = 3 ∧ wf = 1 ∧ te = 1 ∧ we = 1) := by
  have htf : tf ≤ 4 := by omega
  have hte : te ≤ 2 := by omega
  interval_cases tf <;> interval_cases te <;> omega

set_option maxHeartbeats 1200000 in
private theorem mixed_orientation_dichotomy_of_partition
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (rows : Finset α) (cols : Finset β) (family : Finset ι)
    (row : ι → Finset α) (col : ι → Finset β)
    (tallFive wideFive tallEight wideEight : Finset ι)
    (hrowsCard : rows.card = 6) (hcolsCard : cols.card = 6)
    (hrowSub : ∀ i, row i ⊆ rows) (hcolSub : ∀ i, col i ⊆ cols)
    (hcover : ∀ x ∈ rows, ∀ y ∈ cols, ∃ i ∈ family,
      x ∈ row i ∧ y ∈ col i)
    (hdisjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (row i) (row j) ∨ Disjoint (col i) (col j))
    (htallFiveSub : tallFive ⊆ family)
    (hwideFiveSub : wideFive ⊆ family)
    (htallEightSub : tallEight ⊆ family)
    (hwideEightSub : wideEight ⊆ family)
    (htallFiveShape : ∀ i ∈ tallFive,
      (row i).card = 5 ∧ (col i).card = 1)
    (hwideFiveShape : ∀ i ∈ wideFive,
      (row i).card = 1 ∧ (col i).card = 5)
    (htallEightShape : ∀ i ∈ tallEight,
      (row i).card = 4 ∧ (col i).card = 2)
    (hwideEightShape : ∀ i ∈ wideEight,
      (row i).card = 2 ∧ (col i).card = 4)
    (hpartition : family =
      ((tallFive ∪ wideFive) ∪ tallEight) ∪ wideEight)
    (hfiveCard : tallFive.card + wideFive.card = 4)
    (heightCard : tallEight.card + wideEight.card = 2) :
    (tallFive.card = 2 ∧ wideFive.card = 2 ∧
      tallEight.card = 0 ∧ wideEight.card = 2) ∨
    (tallFive.card = 2 ∧ wideFive.card = 2 ∧
      tallEight.card = 2 ∧ wideEight.card = 0) := by
  classical
  have disjoint_of_row_card_ne {left right : Finset ι}
      (hleft : ∀ i ∈ left, (row i).card = 5)
      (hright : ∀ i ∈ right, (row i).card ≠ 5) :
      Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro i hiLeft hiRight
    exact hright i hiRight (hleft i hiLeft)
  have disjoint_of_row_cards_ne {left right : Finset ι} {p q : ℕ}
      (hpq : p ≠ q)
      (hleft : ∀ i ∈ left, (row i).card = p)
      (hright : ∀ i ∈ right, (row i).card = q) :
      Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro i hiLeft hiRight
    exact hpq ((hleft i hiLeft).symm.trans (hright i hiRight))
  have hdTW : Disjoint tallFive wideFive :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (htallFiveShape i hi).1)
      (fun i hi ↦ (hwideFiveShape i hi).1)
  have hdTT8 : Disjoint tallFive tallEight :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (htallFiveShape i hi).1)
      (fun i hi ↦ (htallEightShape i hi).1)
  have hdWT8 : Disjoint wideFive tallEight :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (hwideFiveShape i hi).1)
      (fun i hi ↦ (htallEightShape i hi).1)
  have hdTW8 : Disjoint tallFive wideEight :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (htallFiveShape i hi).1)
      (fun i hi ↦ (hwideEightShape i hi).1)
  have hdWW8 : Disjoint wideFive wideEight :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (hwideFiveShape i hi).1)
      (fun i hi ↦ (hwideEightShape i hi).1)
  have hdT8W8 : Disjoint tallEight wideEight :=
    disjoint_of_row_cards_ne (by omega)
      (fun i hi ↦ (htallEightShape i hi).1)
      (fun i hi ↦ (hwideEightShape i hi).1)
  have hdFirstEight : Disjoint (tallFive ∪ wideFive) tallEight :=
    Finset.disjoint_union_left.mpr ⟨hdTT8, hdWT8⟩
  have hdLast : Disjoint ((tallFive ∪ wideFive) ∪ tallEight) wideEight :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hdTW8, hdWW8⟩, hdT8W8⟩
  let a : α → ℕ := fun x ↦
    (tallFive.filter fun i ↦ x ∈ row i).card
  let b : α → ℕ := fun x ↦
    (wideFive.filter fun i ↦ x ∈ row i).card
  let c : α → ℕ := fun x ↦
    (tallEight.filter fun i ↦ x ∈ row i).card
  let d : α → ℕ := fun x ↦
    (wideEight.filter fun i ↦ x ∈ row i).card
  have hrowTable : ∀ x ∈ rows,
      (a x = 0 ∧ b x = 0 ∧ c x = 1 ∧ d x = 1) ∨
        (a x = 1 ∧ b x = 1 ∧ c x = 0 ∧ d x = 0) ∨
        (a x = 2 ∧ b x = 0 ∧ c x = 0 ∧ d x = 1) ∨
        (a x = 2 ∧ b x = 0 ∧ c x = 2 ∧ d x = 0) ∨
        (a x = 4 ∧ b x = 0 ∧ c x = 1 ∧ d x = 0) := by
    intro x hx
    have hincidence := rectangle_partition_row_incidence_sum rows cols family
      row col hrowSub hcolSub hcover hdisjoint x hx
    rw [hpartition, Finset.sum_union hdLast,
      Finset.sum_union hdFirstEight, Finset.sum_union hdTW] at hincidence
    have htallFiveSum :
        (∑ i ∈ tallFive, if x ∈ row i then (col i).card else 0) = a x := by
      calc
        _ = ∑ i ∈ tallFive, if x ∈ row i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(htallFiveShape i hi).2]
        _ = a x := by
          simpa [a] using sum_ite_const_on_family tallFive row x 1
    have hwideFiveSum :
        (∑ i ∈ wideFive, if x ∈ row i then (col i).card else 0) = 5 * b x := by
      calc
        _ = ∑ i ∈ wideFive, if x ∈ row i then 5 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hwideFiveShape i hi).2]
        _ = 5 * b x := by
          simpa [b, Nat.mul_comm] using
            sum_ite_const_on_family wideFive row x 5
    have htallEightSum :
        (∑ i ∈ tallEight, if x ∈ row i then (col i).card else 0) = 2 * c x := by
      calc
        _ = ∑ i ∈ tallEight, if x ∈ row i then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(htallEightShape i hi).2]
        _ = 2 * c x := by
          simpa [c, Nat.mul_comm] using
            sum_ite_const_on_family tallEight row x 2
    have hwideEightSum :
        (∑ i ∈ wideEight, if x ∈ row i then (col i).card else 0) = 4 * d x := by
      calc
        _ = ∑ i ∈ wideEight, if x ∈ row i then 4 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hwideEightShape i hi).2]
        _ = 4 * d x := by
          simpa [d, Nat.mul_comm] using
            sum_ite_const_on_family wideEight row x 4
    have haLe : a x ≤ 4 := by
      have := Finset.card_filter_le tallFive (fun i ↦ x ∈ row i)
      dsimp [a]
      omega
    have hbLe : b x ≤ 4 := by
      have := Finset.card_filter_le wideFive (fun i ↦ x ∈ row i)
      dsimp [b]
      omega
    have hcLe : c x ≤ 2 := by
      have := Finset.card_filter_le tallEight (fun i ↦ x ∈ row i)
      dsimp [c]
      omega
    have hdLe : d x ≤ 2 := by
      have := Finset.card_filter_le wideEight (fun i ↦ x ∈ row i)
      dsimp [d]
      omega
    apply mixed_local_incidence_table haLe hbLe hcLe hdLe
    rw [hcolsCard] at hincidence
    omega
  obtain ⟨r₀, r₁, r₂, r₃, r₄,
    hrCard, hra, hrb, hrc, hrd⟩ :=
    aggregate_mixed_local_incidence_table rows a b c d hrowTable
  have hraTotal : (∑ x ∈ rows, a x) = 5 * tallFive.card := by
    rw [sum_membership_counts rows tallFive row (fun i hi ↦
      hrowSub i)]
    have hsum := Finset.sum_const_nat
      (s := tallFive) (m := 5) (f := fun i ↦ (row i).card)
      (fun i hi ↦ (htallFiveShape i hi).1)
    simpa [a, Nat.mul_comm] using hsum
  have hrbTotal : (∑ x ∈ rows, b x) = wideFive.card := by
    rw [sum_membership_counts rows wideFive row (fun i hi ↦
      hrowSub i)]
    have hsum := Finset.sum_const_nat
      (s := wideFive) (m := 1) (f := fun i ↦ (row i).card)
      (fun i hi ↦ (hwideFiveShape i hi).1)
    simpa [b] using hsum
  have hrcTotal : (∑ x ∈ rows, c x) = 4 * tallEight.card := by
    rw [sum_membership_counts rows tallEight row (fun i hi ↦
      hrowSub i)]
    have hsum := Finset.sum_const_nat
      (s := tallEight) (m := 4) (f := fun i ↦ (row i).card)
      (fun i hi ↦ (htallEightShape i hi).1)
    simpa [c, Nat.mul_comm] using hsum
  have hrdTotal : (∑ x ∈ rows, d x) = 2 * wideEight.card := by
    rw [sum_membership_counts rows wideEight row (fun i hi ↦
      hrowSub i)]
    have hsum := Finset.sum_const_nat
      (s := wideEight) (m := 2) (f := fun i ↦ (row i).card)
      (fun i hi ↦ (hwideEightShape i hi).1)
    simpa [d, Nat.mul_comm] using hsum
  let a' : β → ℕ := fun y ↦
    (wideFive.filter fun i ↦ y ∈ col i).card
  let b' : β → ℕ := fun y ↦
    (tallFive.filter fun i ↦ y ∈ col i).card
  let c' : β → ℕ := fun y ↦
    (wideEight.filter fun i ↦ y ∈ col i).card
  let d' : β → ℕ := fun y ↦
    (tallEight.filter fun i ↦ y ∈ col i).card
  have hcover' : ∀ y ∈ cols, ∀ x ∈ rows, ∃ i ∈ family,
      y ∈ col i ∧ x ∈ row i := by
    intro y hy x hx
    obtain ⟨i, hi, hxRow, hyCol⟩ := hcover x hx y hy
    exact ⟨i, hi, hyCol, hxRow⟩
  have hdisjoint' : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (col i) (col j) ∨ Disjoint (row i) (row j) := by
    intro i hi j hj hij
    rcases hdisjoint i hi j hj hij with hrows | hcols
    · exact Or.inr hrows
    · exact Or.inl hcols
  have hcolTable : ∀ y ∈ cols,
      (a' y = 0 ∧ b' y = 0 ∧ c' y = 1 ∧ d' y = 1) ∨
        (a' y = 1 ∧ b' y = 1 ∧ c' y = 0 ∧ d' y = 0) ∨
        (a' y = 2 ∧ b' y = 0 ∧ c' y = 0 ∧ d' y = 1) ∨
        (a' y = 2 ∧ b' y = 0 ∧ c' y = 2 ∧ d' y = 0) ∨
        (a' y = 4 ∧ b' y = 0 ∧ c' y = 1 ∧ d' y = 0) := by
    intro y hy
    have hincidence := rectangle_partition_row_incidence_sum cols rows family
      col row hcolSub hrowSub hcover' hdisjoint' y hy
    rw [hpartition, Finset.sum_union hdLast,
      Finset.sum_union hdFirstEight, Finset.sum_union hdTW] at hincidence
    have htallFiveSum :
        (∑ i ∈ tallFive, if y ∈ col i then (row i).card else 0) = 5 * b' y := by
      calc
        _ = ∑ i ∈ tallFive, if y ∈ col i then 5 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(htallFiveShape i hi).1]
        _ = 5 * b' y := by
          simpa [b', Nat.mul_comm] using
            sum_ite_const_on_family tallFive col y 5
    have hwideFiveSum :
        (∑ i ∈ wideFive, if y ∈ col i then (row i).card else 0) = a' y := by
      calc
        _ = ∑ i ∈ wideFive, if y ∈ col i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hwideFiveShape i hi).1]
        _ = a' y := by
          simpa [a'] using sum_ite_const_on_family wideFive col y 1
    have htallEightSum :
        (∑ i ∈ tallEight, if y ∈ col i then (row i).card else 0) = 4 * d' y := by
      calc
        _ = ∑ i ∈ tallEight, if y ∈ col i then 4 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(htallEightShape i hi).1]
        _ = 4 * d' y := by
          simpa [d', Nat.mul_comm] using
            sum_ite_const_on_family tallEight col y 4
    have hwideEightSum :
        (∑ i ∈ wideEight, if y ∈ col i then (row i).card else 0) = 2 * c' y := by
      calc
        _ = ∑ i ∈ wideEight, if y ∈ col i then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hwideEightShape i hi).1]
        _ = 2 * c' y := by
          simpa [c', Nat.mul_comm] using
            sum_ite_const_on_family wideEight col y 2
    have haLe : a' y ≤ 4 := by
      have := Finset.card_filter_le wideFive (fun i ↦ y ∈ col i)
      dsimp [a']
      omega
    have hbLe : b' y ≤ 4 := by
      have := Finset.card_filter_le tallFive (fun i ↦ y ∈ col i)
      dsimp [b']
      omega
    have hcLe : c' y ≤ 2 := by
      have := Finset.card_filter_le wideEight (fun i ↦ y ∈ col i)
      dsimp [c']
      omega
    have hdLe : d' y ≤ 2 := by
      have := Finset.card_filter_le tallEight (fun i ↦ y ∈ col i)
      dsimp [d']
      omega
    apply mixed_local_incidence_table haLe hbLe hcLe hdLe
    rw [hrowsCard] at hincidence
    omega
  obtain ⟨s₀, s₁, s₂, s₃, s₄,
    hsCard, hsa, hsb, hsc, hsd⟩ :=
    aggregate_mixed_local_incidence_table cols a' b' c' d' hcolTable
  have hsaTotal : (∑ y ∈ cols, a' y) = 5 * wideFive.card := by
    rw [sum_membership_counts cols wideFive col (fun i hi ↦
      hcolSub i)]
    have hsum := Finset.sum_const_nat
      (s := wideFive) (m := 5) (f := fun i ↦ (col i).card)
      (fun i hi ↦ (hwideFiveShape i hi).2)
    simpa [a', Nat.mul_comm] using hsum
  have hsbTotal : (∑ y ∈ cols, b' y) = tallFive.card := by
    rw [sum_membership_counts cols tallFive col (fun i hi ↦
      hcolSub i)]
    have hsum := Finset.sum_const_nat
      (s := tallFive) (m := 1) (f := fun i ↦ (col i).card)
      (fun i hi ↦ (htallFiveShape i hi).2)
    simpa [b'] using hsum
  have hscTotal : (∑ y ∈ cols, c' y) = 4 * wideEight.card := by
    rw [sum_membership_counts cols wideEight col (fun i hi ↦
      hcolSub i)]
    have hsum := Finset.sum_const_nat
      (s := wideEight) (m := 4) (f := fun i ↦ (col i).card)
      (fun i hi ↦ (hwideEightShape i hi).2)
    simpa [c', Nat.mul_comm] using hsum
  have hsdTotal : (∑ y ∈ cols, d' y) = 2 * tallEight.card := by
    rw [sum_membership_counts cols tallEight col (fun i hi ↦
      hcolSub i)]
    have hsum := Finset.sum_const_nat
      (s := tallEight) (m := 2) (f := fun i ↦ (col i).card)
      (fun i hi ↦ (htallEightShape i hi).2)
    simpa [d', Nat.mul_comm] using hsum
  rw [hrowsCard] at hrCard
  rw [hcolsCard] at hsCard
  have harithmetic :
      (tallFive.card = 1 ∧ wideFive.card = 3 ∧
        tallEight.card = 1 ∧ wideEight.card = 1) ∨
      (tallFive.card = 2 ∧ wideFive.card = 2 ∧
        tallEight.card = 0 ∧ wideEight.card = 2) ∨
      (tallFive.card = 2 ∧ wideFive.card = 2 ∧
        tallEight.card = 1 ∧ wideEight.card = 1) ∨
      (tallFive.card = 2 ∧ wideFive.card = 2 ∧
        tallEight.card = 2 ∧ wideEight.card = 0) ∨
      (tallFive.card = 3 ∧ wideFive.card = 1 ∧
        tallEight.card = 1 ∧ wideEight.card = 1) := by
    apply mixed_orientation_arithmetic hfiveCard heightCard hrCard
    · exact hra.symm.trans hraTotal
    · exact hrb.symm.trans hrbTotal
    · exact hrc.symm.trans hrcTotal
    · exact hrd.symm.trans hrdTotal
    · exact hsCard
    · exact hsa.symm.trans hsaTotal
    · exact hsb.symm.trans hsbTotal
    · exact hsc.symm.trans hscTotal
    · exact hsd.symm.trans hsdTotal
  rcases harithmetic with hbad | hgood | hbad | hgood | hbad
  · exfalso
    obtain ⟨tf, htf⟩ := Finset.card_pos.mp (by omega : 0 < tallFive.card)
    obtain ⟨wf, hwf⟩ := Finset.card_pos.mp (by omega : 0 < wideFive.card)
    obtain ⟨te, hte⟩ := Finset.card_pos.mp (by omega : 0 < tallEight.card)
    obtain ⟨we, hwe⟩ := Finset.card_pos.mp (by omega : 0 < wideEight.card)
    exact opposite_eight_orientations_impossible rows cols family row col
      hrowsCard hcolsCard hrowSub hcolSub hdisjoint
      (htallFiveSub htf) (hwideFiveSub hwf) (htallEightSub hte)
      (hwideEightSub hwe) (htallFiveShape tf htf) (hwideFiveShape wf hwf)
      (htallEightShape te hte) (hwideEightShape we hwe)
  · exact Or.inl hgood
  · exfalso
    obtain ⟨tf, htf⟩ := Finset.card_pos.mp (by omega : 0 < tallFive.card)
    obtain ⟨wf, hwf⟩ := Finset.card_pos.mp (by omega : 0 < wideFive.card)
    obtain ⟨te, hte⟩ := Finset.card_pos.mp (by omega : 0 < tallEight.card)
    obtain ⟨we, hwe⟩ := Finset.card_pos.mp (by omega : 0 < wideEight.card)
    exact opposite_eight_orientations_impossible rows cols family row col
      hrowsCard hcolsCard hrowSub hcolSub hdisjoint
      (htallFiveSub htf) (hwideFiveSub hwf) (htallEightSub hte)
      (hwideEightSub hwe) (htallFiveShape tf htf) (hwideFiveShape wf hwf)
      (htallEightShape te hte) (hwideEightShape we hwe)
  · exact Or.inr hgood
  · exfalso
    obtain ⟨tf, htf⟩ := Finset.card_pos.mp (by omega : 0 < tallFive.card)
    obtain ⟨wf, hwf⟩ := Finset.card_pos.mp (by omega : 0 < wideFive.card)
    obtain ⟨te, hte⟩ := Finset.card_pos.mp (by omega : 0 < tallEight.card)
    obtain ⟨we, hwe⟩ := Finset.card_pos.mp (by omega : 0 < wideEight.card)
    exact opposite_eight_orientations_impossible rows cols family row col
      hrowsCard hcolsCard hrowSub hcolSub hdisjoint
      (htallFiveSub htf) (hwideFiveSub hwf) (htallEightSub hte)
      (hwideEightSub hwe) (htallFiveShape tf htf) (hwideFiveShape wf hwf)
      (htallEightShape te hte) (hwideEightShape we hwe)

private theorem exists_erase_eq_of_card_five
    {α : Type*} [DecidableEq α] {ambientSet side : Finset α}
    (hambient : ambientSet.card = 6) (hsub : side ⊆ ambientSet)
    (hside : side.card = 5) :
    ∃ p ∈ ambientSet, side = ambientSet.erase p := by
  have hdiffCard : (ambientSet \ side).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hambient, hside]
  obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hpDiff : p ∈ ambientSet \ side := by
    rw [hpEq]
    simp
  refine ⟨p, (Finset.mem_sdiff.mp hpDiff).1, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun hxp ↦ (Finset.mem_sdiff.mp hpDiff).2 (hxp ▸ hx), hsub hx⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hpDiff).1, hambient,
      hside]

private theorem exists_singleton_eq_of_card_one
    {α : Type*} [DecidableEq α] {ambientSet side : Finset α}
    (hsub : side ⊆ ambientSet) (hside : side.card = 1) :
    ∃ p ∈ ambientSet, side = {p} := by
  obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hside
  refine ⟨p, hsub (by rw [hpEq]; simp), hpEq⟩

private theorem four_cross_alternatives_force_matching
    {α : Type*} {p q c d r s e f : α}
    (hcNeD : c ≠ d) (hrNeS : r ≠ s)
    (hA₀B₀ : r = p ∨ e = c) (hA₁B₀ : r = q ∨ e = d)
    (hA₀B₁ : s = p ∨ f = c) (hA₁B₁ : s = q ∨ f = d) :
    (r = p ∧ e = d ∧ s = q ∧ f = c) ∨
      (r = q ∧ e = c ∧ s = p ∧ f = d) := by
  rcases hA₀B₀ with h | h <;> rcases hA₁B₀ with h' | h' <;>
    rcases hA₀B₁ with h'' | h'' <;> rcases hA₁B₁ with h''' | h''' <;>
    aesop

private theorem union_three_pairs_eq_six_insertions
    {α : Type*} [DecidableEq α] (a b c d e f : α) :
    ((({a, b} : Finset α) ∪ {c, d}) ∪ {e, f}) =
      {a, b, c, d, e, f} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

set_option maxHeartbeats 1600000 in
private theorem short_first_normal_form_of_oriented_partition
    {n : ℕ} (first second : Finset (Fin n))
    (witnesses tallFive wideFive wideEight : Finset (Finset (Fin n)))
    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)
    (hwitnessCard : witnesses.card = 6)
    (htallFiveCard : tallFive.card = 2)
    (hwideFiveCard : wideFive.card = 2)
    (hwideEightCard : wideEight.card = 2)
    (htallFiveSub : tallFive ⊆ witnesses)
    (hwideFiveSub : wideFive ⊆ witnesses)
    (hwideEightSub : wideEight ⊆ witnesses)
    (htallFiveShape : ∀ third ∈ tallFive,
      (first \ third).card = 5 ∧ (second \ third).card = 1)
    (hwideFiveShape : ∀ third ∈ wideFive,
      (first \ third).card = 1 ∧ (second \ third).card = 5)
    (hwideEightShape : ∀ third ∈ wideEight,
      (first \ third).card = 2 ∧ (second \ third).card = 4)
    (hpartition : witnesses = (tallFive ∪ wideFive) ∪ wideEight)
    (hdisjoint : ∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses,
      third₁ ≠ third₂ →
      Disjoint (first \ third₁) (first \ third₂) ∨
        Disjoint (second \ third₁) (second \ third₂)) :
    IsShortFirstMixedOmissionNormalForm567 first second witnesses := by
  classical
  obtain ⟨A₀, A₁, hAne, htallFiveEq⟩ :=
    Finset.card_eq_two.mp htallFiveCard
  obtain ⟨B₀, B₁, hBne, hwideFiveEq⟩ :=
    Finset.card_eq_two.mp hwideFiveCard
  obtain ⟨D₀, D₁, hDne, hwideEightEq⟩ :=
    Finset.card_eq_two.mp hwideEightCard
  have hA₀Mem : A₀ ∈ tallFive := by rw [htallFiveEq]; simp
  have hA₁Mem : A₁ ∈ tallFive := by rw [htallFiveEq]; simp
  have hB₀Mem : B₀ ∈ wideFive := by rw [hwideFiveEq]; simp
  have hB₁Mem : B₁ ∈ wideFive := by rw [hwideFiveEq]; simp
  have hD₀Mem : D₀ ∈ wideEight := by rw [hwideEightEq]; simp
  have hD₁Mem : D₁ ∈ wideEight := by rw [hwideEightEq]; simp
  have hA₀Shape := htallFiveShape A₀ hA₀Mem
  have hA₁Shape := htallFiveShape A₁ hA₁Mem
  have hB₀Shape := hwideFiveShape B₀ hB₀Mem
  have hB₁Shape := hwideFiveShape B₁ hB₁Mem
  have hD₀Shape := hwideEightShape D₀ hD₀Mem
  have hD₁Shape := hwideEightShape D₁ hD₁Mem
  obtain ⟨p, hpFirst, hA₀Row⟩ := exists_erase_eq_of_card_five
    hfirstCard Finset.sdiff_subset hA₀Shape.1
  obtain ⟨q, hqFirst, hA₁Row⟩ := exists_erase_eq_of_card_five
    hfirstCard Finset.sdiff_subset hA₁Shape.1
  obtain ⟨c, hcSecond, hA₀Col⟩ := exists_singleton_eq_of_card_one
    Finset.sdiff_subset hA₀Shape.2
  obtain ⟨d, hdSecond, hA₁Col⟩ := exists_singleton_eq_of_card_one
    Finset.sdiff_subset hA₁Shape.2
  obtain ⟨r, hrFirst, hB₀Row⟩ := exists_singleton_eq_of_card_one
    Finset.sdiff_subset hB₀Shape.1
  obtain ⟨s, hsFirst, hB₁Row⟩ := exists_singleton_eq_of_card_one
    Finset.sdiff_subset hB₁Shape.1
  obtain ⟨e, heSecond, hB₀Col⟩ := exists_erase_eq_of_card_five
    hsecondCard Finset.sdiff_subset hB₀Shape.2
  obtain ⟨f, hfSecond, hB₁Col⟩ := exists_erase_eq_of_card_five
    hsecondCard Finset.sdiff_subset hB₁Shape.2
  have hA₀Witness : A₀ ∈ witnesses := htallFiveSub hA₀Mem
  have hA₁Witness : A₁ ∈ witnesses := htallFiveSub hA₁Mem
  have hB₀Witness : B₀ ∈ witnesses := hwideFiveSub hB₀Mem
  have hB₁Witness : B₁ ∈ witnesses := hwideFiveSub hB₁Mem
  have hD₀Witness : D₀ ∈ witnesses := hwideEightSub hD₀Mem
  have hD₁Witness : D₁ ∈ witnesses := hwideEightSub hD₁Mem
  have hcNeD : c ≠ d := by
    have hcols : Disjoint (second \ A₀) (second \ A₁) := by
      rcases hdisjoint A₀ hA₀Witness A₁ hA₁Witness hAne with hrows | hcols
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          Finset.sdiff_subset Finset.sdiff_subset (by
            rw [hfirstCard, hA₀Shape.1, hA₁Shape.1]
            omega) hrows).elim
      · exact hcols
    intro hcd
    exact (Finset.disjoint_left.mp hcols) (a := c)
      (by rw [hA₀Col]; simp) (by rw [hA₁Col, hcd]; simp)
  have hrNeS : r ≠ s := by
    have hrows : Disjoint (first \ B₀) (first \ B₁) := by
      rcases hdisjoint B₀ hB₀Witness B₁ hB₁Witness hBne with hrows | hcols
      · exact hrows
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          Finset.sdiff_subset Finset.sdiff_subset (by
            rw [hsecondCard, hB₀Shape.2, hB₁Shape.2]
            omega) hcols).elim
    intro hrs
    exact (Finset.disjoint_left.mp hrows) (a := r)
      (by rw [hB₀Row]; simp) (by rw [hB₁Row, hrs]; simp)
  have cross_alternative (A B : Finset (Fin n))
      (hAWitness : A ∈ witnesses) (hBWitness : B ∈ witnesses)
      (hAB : A ≠ B) (u v x y : Fin n)
      (hu : u ∈ first) (hv : v ∈ first) (hx : x ∈ second)
      (hARow : first \ A = first.erase u)
      (hACol : second \ A = {x})
      (hBRow : first \ B = {v})
      (hBCol : second \ B = second.erase y) :
      v = u ∨ y = x := by
    rcases hdisjoint A hAWitness B hBWitness hAB with hrows | hcols
    · left
      by_contra hvu
      exact (Finset.disjoint_left.mp hrows) (a := v)
        (by rw [hARow]; exact Finset.mem_erase.mpr ⟨hvu, hv⟩)
        (by rw [hBRow]; simp)
    · right
      by_contra hyx
      exact (Finset.disjoint_left.mp hcols) (a := x)
        (by rw [hACol]; simp)
        (by rw [hBCol]; exact Finset.mem_erase.mpr ⟨Ne.symm hyx, hx⟩)
  have hA₀B₀Ne : A₀ ≠ B₀ := by
    intro h
    subst B₀
    omega
  have hA₁B₀Ne : A₁ ≠ B₀ := by
    intro h
    subst B₀
    omega
  have hA₀B₁Ne : A₀ ≠ B₁ := by
    intro h
    subst B₁
    omega
  have hA₁B₁Ne : A₁ ≠ B₁ := by
    intro h
    subst B₁
    omega
  have hA₀B₀ := cross_alternative A₀ B₀ hA₀Witness hB₀Witness
    hA₀B₀Ne p r c e hpFirst hrFirst hcSecond hA₀Row hA₀Col hB₀Row hB₀Col
  have hA₁B₀ := cross_alternative A₁ B₀ hA₁Witness hB₀Witness
    hA₁B₀Ne q r d e hqFirst hrFirst hdSecond hA₁Row hA₁Col hB₀Row hB₀Col
  have hA₀B₁ := cross_alternative A₀ B₁ hA₀Witness hB₁Witness
    hA₀B₁Ne p s c f hpFirst hsFirst hcSecond hA₀Row hA₀Col hB₁Row hB₁Col
  have hA₁B₁ := cross_alternative A₁ B₁ hA₁Witness hB₁Witness
    hA₁B₁Ne q s d f hqFirst hsFirst hdSecond hA₁Row hA₁Col hB₁Row hB₁Col
  have hmatching :
      (r = p ∧ e = d ∧ s = q ∧ f = c) ∨
        (r = q ∧ e = c ∧ s = p ∧ f = d) := by
    exact four_cross_alternatives_force_matching hcNeD hrNeS
      hA₀B₀ hA₁B₀ hA₀B₁ hA₁B₁
  have reconstruct (Bleft Bright : Finset (Fin n))
      (hBleftWitness : Bleft ∈ witnesses)
      (hBrightWitness : Bright ∈ witnesses)
      (hBleftNeBright : Bleft ≠ Bright)
      (hwideFiveOriented : wideFive = {Bleft, Bright})
      (hBleftRow : first \ Bleft = {p})
      (hBleftCol : second \ Bleft = second.erase d)
      (hBrightRow : first \ Bright = {q})
      (hBrightCol : second \ Bright = second.erase c) :
      IsShortFirstMixedOmissionNormalForm567 first second witnesses := by
    have hpNeQ : p ≠ q := by
      intro hpq
      subst q
      have hrows : Disjoint (first \ Bleft) (first \ Bright) := by
        rcases hdisjoint Bleft hBleftWitness Bright hBrightWitness
            hBleftNeBright with
          hrows | hcols
        · exact hrows
        · exact (not_disjoint_of_card_lt_add_of_subset_mixed
            Finset.sdiff_subset Finset.sdiff_subset (by
              rw [hsecondCard]
              have hleftCard : (second \ Bleft).card = 5 := by
                rw [hBleftCol, Finset.card_erase_of_mem hdSecond, hsecondCard]
              have hrightCard : (second \ Bright).card = 5 := by
                rw [hBrightCol, Finset.card_erase_of_mem hcSecond, hsecondCard]
              omega) hcols).elim
      exact (Finset.disjoint_left.mp hrows) (a := p)
        (by rw [hBleftRow]; simp) (by rw [hBrightRow]; simp)
    let P := first \ D₀
    let Q := first \ D₁
    have d_col_eq (D : Finset (Fin n)) (hDWitness : D ∈ witnesses)
        (hDShape : (first \ D).card = 2 ∧ (second \ D).card = 4) :
        second \ D = (second.erase c).erase d := by
      have hcolA₀ : Disjoint (second \ D) (second \ A₀) := by
        have hDNeA₀ : D ≠ A₀ := by intro h; subst D; omega
        rcases hdisjoint D hDWitness A₀ hA₀Witness hDNeA₀ with hrow | hcol
        · exact (not_disjoint_of_card_lt_add_of_subset_mixed
            Finset.sdiff_subset Finset.sdiff_subset (by
              rw [hfirstCard, hDShape.1, hA₀Shape.1]
              omega) hrow).elim
        · exact hcol
      have hcolA₁ : Disjoint (second \ D) (second \ A₁) := by
        have hDNeA₁ : D ≠ A₁ := by intro h; subst D; omega
        rcases hdisjoint D hDWitness A₁ hA₁Witness hDNeA₁ with hrow | hcol
        · exact (not_disjoint_of_card_lt_add_of_subset_mixed
            Finset.sdiff_subset Finset.sdiff_subset (by
              rw [hfirstCard, hDShape.1, hA₁Shape.1]
              omega) hrow).elim
        · exact hcol
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        have hxSecond := Finset.mem_sdiff.mp hx |>.1
        have hxNeC : x ≠ c := by
          intro hxc
          subst x
          exact (Finset.disjoint_left.mp hcolA₀) (a := c) hx
            (by rw [hA₀Col]; simp)
        have hxNeD : x ≠ d := by
          intro hxd
          subst x
          exact (Finset.disjoint_left.mp hcolA₁) (a := d) hx
            (by rw [hA₁Col]; simp)
        exact Finset.mem_erase.mpr
          ⟨hxNeD, Finset.mem_erase.mpr ⟨hxNeC, hxSecond⟩⟩
      · rw [Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hcNeD.symm, hdSecond⟩),
          Finset.card_erase_of_mem hcSecond, hsecondCard, hDShape.2]
    have hD₀Col := d_col_eq D₀ hD₀Witness hD₀Shape
    have hD₁Col := d_col_eq D₁ hD₁Witness hD₁Shape
    have d_row_sub (D : Finset (Fin n)) (hDWitness : D ∈ witnesses)
        (hDShape : (first \ D).card = 2 ∧ (second \ D).card = 4) :
        first \ D ⊆ (first.erase p).erase q := by
      have hrowBL : Disjoint (first \ D) (first \ Bleft) := by
        have hDNeBL : D ≠ Bleft := by
          intro h
          subst D
          have := hDShape.1
          rw [hBleftRow] at this
          simp at this
        rcases hdisjoint D hDWitness Bleft hBleftWitness hDNeBL with hrow | hcol
        · exact hrow
        · exact (not_disjoint_of_card_lt_add_of_subset_mixed
            Finset.sdiff_subset Finset.sdiff_subset (by
              have hBLCard : (second \ Bleft).card = 5 := by
                rw [hBleftCol, Finset.card_erase_of_mem hdSecond, hsecondCard]
              rw [hsecondCard, hDShape.2, hBLCard]
              omega) hcol).elim
      have hrowBR : Disjoint (first \ D) (first \ Bright) := by
        have hDNeBR : D ≠ Bright := by
          intro h
          subst D
          have := hDShape.1
          rw [hBrightRow] at this
          simp at this
        rcases hdisjoint D hDWitness Bright hBrightWitness hDNeBR with hrow | hcol
        · exact hrow
        · exact (not_disjoint_of_card_lt_add_of_subset_mixed
            Finset.sdiff_subset Finset.sdiff_subset (by
              have hBRCard : (second \ Bright).card = 5 := by
                rw [hBrightCol, Finset.card_erase_of_mem hcSecond, hsecondCard]
              rw [hsecondCard, hDShape.2, hBRCard]
              omega) hcol).elim
      intro x hx
      have hxFirst := Finset.mem_sdiff.mp hx |>.1
      have hxNeP : x ≠ p := by
        intro hxp
        subst x
        exact (Finset.disjoint_left.mp hrowBL) (a := p) hx
          (by rw [hBleftRow]; simp)
      have hxNeQ : x ≠ q := by
        intro hxq
        subst x
        exact (Finset.disjoint_left.mp hrowBR) (a := q) hx
          (by rw [hBrightRow]; simp)
      exact Finset.mem_erase.mpr
        ⟨hxNeQ, Finset.mem_erase.mpr ⟨hxNeP, hxFirst⟩⟩
    have hD₀RowSub := d_row_sub D₀ hD₀Witness hD₀Shape
    have hD₁RowSub := d_row_sub D₁ hD₁Witness hD₁Shape
    have hDRows : Disjoint (first \ D₀) (first \ D₁) := by
      rcases hdisjoint D₀ hD₀Witness D₁ hD₁Witness hDne with hrow | hcol
      · exact hrow
      · exact (not_disjoint_of_card_lt_add_of_subset_mixed
          Finset.sdiff_subset Finset.sdiff_subset (by
            rw [hsecondCard, hD₀Shape.2, hD₁Shape.2]
            omega) hcol).elim
    have hrestCard : ((first.erase p).erase q).card = 4 := by
      rw [Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hpNeQ.symm, hqFirst⟩),
        Finset.card_erase_of_mem hpFirst, hfirstCard]
    have hDUnion : (first \ D₀) ∪ (first \ D₁) =
        (first.erase p).erase q := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.union_subset hD₀RowSub hD₁RowSub
      · rw [Finset.card_union_of_disjoint hDRows,
          hD₀Shape.1, hD₁Shape.1, hrestCard]
    have hWitnessEq : witnesses = {A₀, A₁, Bleft, Bright, D₀, D₁} := by
      rw [hpartition, htallFiveEq, hwideFiveOriented, hwideEightEq]
      exact union_three_pairs_eq_six_insertions A₀ A₁ Bleft Bright D₀ D₁
    have hExplicitCard :
        ({A₀, A₁, Bleft, Bright, D₀, D₁} :
          Finset (Finset (Fin n))).card = 6 := by
      rw [← hWitnessEq]
      exact hwitnessCard
    unfold IsShortFirstMixedOmissionNormalForm567
    refine ⟨p, q, c, d, P, Q, A₀, A₁, Bleft, Bright, D₀, D₁,
      hpFirst, hqFirst, hcSecond, hdSecond, hpNeQ, hcNeD,
      ?_, ?_, hDRows, ?_, hWitnessEq, hExplicitCard,
      hA₀Row, hA₀Col, hA₁Row, hA₁Col, hBleftRow, hBleftCol,
      hBrightRow, hBrightCol, rfl, hD₀Col, rfl, hD₁Col⟩
    · simpa [P] using hD₀Shape.1
    · simpa [Q] using hD₁Shape.1
    simpa [P, Q] using hDUnion
  rcases hmatching with hmatch | hmatch
  · rcases hmatch with ⟨rfl, rfl, rfl, rfl⟩
    exact reconstruct B₀ B₁ hB₀Witness hB₁Witness hBne hwideFiveEq
      hB₀Row hB₀Col hB₁Row hB₁Col
  · rcases hmatch with ⟨rfl, rfl, rfl, rfl⟩
    exact reconstruct B₁ B₀ hB₁Witness hB₀Witness hBne.symm
      (by simpa [Finset.pair_comm] using hwideFiveEq)
      hB₁Row hB₁Col hB₀Row hB₀Col

set_option maxHeartbeats 1600000 in
/-- The exact mixed omission profile has one of the two explicit six-witness
normal forms. -/
theorem IsCarrierOnlyOmissionRectangleSystem567.mixed_normalForm
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem :
      IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfive : OmissionAreaCount567 first second witnesses 5 = 4)
    (height : OmissionAreaCount567 first second witnesses 8 = 2)
    (hnine : OmissionAreaCount567 first second witnesses 9 = 0) :
    IsShortFirstMixedOmissionNormalForm567 first second witnesses ∨
      IsShortSecondMixedOmissionNormalForm567 first second witnesses := by
  classical
  obtain ⟨hfirstCard, hsecondCard⟩ :=
    hsystem.carrier_cards_eq_six_of_mixed hfive height
  let row : Finset (Fin n) → Finset (Fin n) := fun third ↦ first \ third
  let col : Finset (Fin n) → Finset (Fin n) := fun third ↦ second \ third
  let tallFive := witnesses.filter fun third ↦
    (row third).card = 5 ∧ (col third).card = 1
  let wideFive := witnesses.filter fun third ↦
    (row third).card = 1 ∧ (col third).card = 5
  let tallEight := witnesses.filter fun third ↦
    (row third).card = 4 ∧ (col third).card = 2
  let wideEight := witnesses.filter fun third ↦
    (row third).card = 2 ∧ (col third).card = 4
  let fiveFamily := witnesses.filter fun third ↦
    (row third).card * (col third).card = 5
  let eightFamily := witnesses.filter fun third ↦
    (row third).card * (col third).card = 8
  let nineFamily := witnesses.filter fun third ↦
    (row third).card * (col third).card = 9
  have htallFiveSub : tallFive ⊆ witnesses := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).1
  have hwideFiveSub : wideFive ⊆ witnesses := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).1
  have htallEightSub : tallEight ⊆ witnesses := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).1
  have hwideEightSub : wideEight ⊆ witnesses := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).1
  have htallFiveShape : ∀ third ∈ tallFive,
      (row third).card = 5 ∧ (col third).card = 1 := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).2
  have hwideFiveShape : ∀ third ∈ wideFive,
      (row third).card = 1 ∧ (col third).card = 5 := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).2
  have htallEightShape : ∀ third ∈ tallEight,
      (row third).card = 4 ∧ (col third).card = 2 := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).2
  have hwideEightShape : ∀ third ∈ wideEight,
      (row third).card = 2 ∧ (col third).card = 4 := by
    intro third hthird
    exact (Finset.mem_filter.mp hthird).2
  have hfiveFamily : fiveFamily = tallFive ∪ wideFive := by
    ext third
    simp only [fiveFamily, tallFive, wideFive, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro hthird
      have harea := hthird.2
      have hshape :=
        (hsystem.1 third hthird.1).omission_shape hfirstCard hsecondCard
      change
        (((row third).card = 5 ∧ (col third).card = 1) ∨
          ((row third).card = 4 ∧ (col third).card = 2) ∨
          ((row third).card = 3 ∧ (col third).card = 3) ∨
          ((row third).card = 2 ∧ (col third).card = 4) ∨
          ((row third).card = 1 ∧ (col third).card = 5)) at hshape
      rcases hshape with h | h | h | h | h
      · exact Or.inl ⟨hthird.1, h⟩
      · rw [h.1, h.2] at harea
        norm_num at harea
      · rw [h.1, h.2] at harea
        norm_num at harea
      · rw [h.1, h.2] at harea
        norm_num at harea
      · exact Or.inr ⟨hthird.1, h⟩
    · rintro (⟨hthird, hshape⟩ | ⟨hthird, hshape⟩)
      · exact ⟨hthird, by rw [hshape.1, hshape.2]⟩
      · exact ⟨hthird, by rw [hshape.1, hshape.2]⟩
  have heightFamily : eightFamily = tallEight ∪ wideEight := by
    ext third
    simp only [eightFamily, tallEight, wideEight, Finset.mem_filter,
      Finset.mem_union]
    constructor
    · intro hthird
      have harea := hthird.2
      have hshape :=
        (hsystem.1 third hthird.1).omission_shape hfirstCard hsecondCard
      change
        (((row third).card = 5 ∧ (col third).card = 1) ∨
          ((row third).card = 4 ∧ (col third).card = 2) ∨
          ((row third).card = 3 ∧ (col third).card = 3) ∨
          ((row third).card = 2 ∧ (col third).card = 4) ∨
          ((row third).card = 1 ∧ (col third).card = 5)) at hshape
      rcases hshape with h | h | h | h | h
      · rw [h.1, h.2] at harea
        norm_num at harea
      · exact Or.inl ⟨hthird.1, h⟩
      · rw [h.1, h.2] at harea
        norm_num at harea
      · exact Or.inr ⟨hthird.1, h⟩
      · rw [h.1, h.2] at harea
        norm_num at harea
    · rintro (⟨hthird, hshape⟩ | ⟨hthird, hshape⟩)
      · exact ⟨hthird, by rw [hshape.1, hshape.2]⟩
      · exact ⟨hthird, by rw [hshape.1, hshape.2]⟩
  have hfiveFamilyCard : fiveFamily.card = 4 := by
    simpa [fiveFamily, row, col, OmissionAreaCount567] using hfive
  have heightFamilyCard : eightFamily.card = 2 := by
    simpa [eightFamily, row, col, OmissionAreaCount567] using height
  have hnineFamilyCard : nineFamily.card = 0 := by
    simpa [nineFamily, row, col, OmissionAreaCount567] using hnine
  have hnineFamilyEmpty : nineFamily = ∅ :=
    Finset.card_eq_zero.mp hnineFamilyCard
  have hdTallWideFive : Disjoint tallFive wideFive := by
    apply Finset.disjoint_left.mpr
    intro third htall hwide
    have htallShape := htallFiveShape third htall
    have hwideShape := hwideFiveShape third hwide
    omega
  have hdTallWideEight : Disjoint tallEight wideEight := by
    apply Finset.disjoint_left.mpr
    intro third htall hwide
    have htallShape := htallEightShape third htall
    have hwideShape := hwideEightShape third hwide
    omega
  have hfiveCard : tallFive.card + wideFive.card = 4 := by
    rw [hfiveFamily, Finset.card_union_of_disjoint hdTallWideFive] at hfiveFamilyCard
    exact hfiveFamilyCard
  have heightCard : tallEight.card + wideEight.card = 2 := by
    rw [heightFamily, Finset.card_union_of_disjoint hdTallWideEight] at heightFamilyCard
    exact heightFamilyCard
  have hpartition : witnesses =
      ((tallFive ∪ wideFive) ∪ tallEight) ∪ wideEight := by
    ext third
    constructor
    · intro hthird
      have hshape :=
        (hsystem.1 third hthird).omission_shape hfirstCard hsecondCard
      change
        (((row third).card = 5 ∧ (col third).card = 1) ∨
          ((row third).card = 4 ∧ (col third).card = 2) ∨
          ((row third).card = 3 ∧ (col third).card = 3) ∨
          ((row third).card = 2 ∧ (col third).card = 4) ∨
          ((row third).card = 1 ∧ (col third).card = 5)) at hshape
      simp only [Finset.mem_union]
      rcases hshape with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hthird, h⟩)))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hthird, h⟩))
      · exfalso
        have hthirdNine : third ∈ nineFamily := by
          exact Finset.mem_filter.mpr ⟨hthird, by rw [h.1, h.2]⟩
        rw [hnineFamilyEmpty] at hthirdNine
        simp at hthirdNine
      · exact Or.inr (Finset.mem_filter.mpr ⟨hthird, h⟩)
      · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hthird, h⟩)))
    · intro hthird
      simp only [Finset.mem_union] at hthird
      rcases hthird with ((htall | hwide) | height) | hwideEight
      · exact htallFiveSub htall
      · exact hwideFiveSub hwide
      · exact htallEightSub height
      · exact hwideEightSub hwideEight
  have hcover : ∀ x ∈ first, ∀ y ∈ second, ∃ third ∈ witnesses,
      x ∈ row third ∧ y ∈ col third := by
    intro x hx y hy
    obtain ⟨third, hthird, hpair⟩ := hsystem.2.1 x hx y hy
    have hpairData := Finset.mem_product.mp hpair
    exact ⟨third, hthird, hpairData.1, hpairData.2⟩
  have hsideDisjoint : ∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses,
      third₁ ≠ third₂ →
      Disjoint (row third₁) (row third₂) ∨
        Disjoint (col third₁) (col third₂) := by
    intro third₁ hthird₁ third₂ hthird₂ hne
    apply Finset.disjoint_product.mp
    simpa [row, col, CarrierOnlyOmissionRectangle567] using
      hsystem.2.2 third₁ hthird₁ third₂ hthird₂ hne
  have horientation := mixed_orientation_dichotomy_of_partition
    first second witnesses row col tallFive wideFive tallEight wideEight
    hfirstCard hsecondCard (fun _ ↦ Finset.sdiff_subset)
    (fun _ ↦ Finset.sdiff_subset) hcover hsideDisjoint
    htallFiveSub hwideFiveSub htallEightSub hwideEightSub
    htallFiveShape hwideFiveShape htallEightShape hwideEightShape
    hpartition hfiveCard heightCard
  have hwitnessCard : witnesses.card = 6 := by
    have hequations :=
      hsystem.omission_area_equations hfirstCard hsecondCard
    omega
  rcases horientation with hshortFirst | hshortSecond
  · left
    have htallEightEmpty : tallEight = ∅ :=
      Finset.card_eq_zero.mp hshortFirst.2.2.1
    have hshortPartition : witnesses =
        (tallFive ∪ wideFive) ∪ wideEight := by
      simpa [htallEightEmpty] using hpartition
    exact short_first_normal_form_of_oriented_partition
      first second witnesses tallFive wideFive wideEight
      hfirstCard hsecondCard hwitnessCard hshortFirst.1 hshortFirst.2.1
      hshortFirst.2.2.2 htallFiveSub hwideFiveSub hwideEightSub
      (by simpa [row, col] using htallFiveShape)
      (by simpa [row, col] using hwideFiveShape)
      (by simpa [row, col] using hwideEightShape)
      hshortPartition (by simpa [row, col] using hsideDisjoint)
  · right
    unfold IsShortSecondMixedOmissionNormalForm567
    have hwideEightEmpty : wideEight = ∅ :=
      Finset.card_eq_zero.mp hshortSecond.2.2.2
    have hshortPartition : witnesses =
        (wideFive ∪ tallFive) ∪ tallEight := by
      have h := hpartition
      rw [hwideEightEmpty] at h
      simp only [Finset.union_empty] at h
      simpa [Finset.union_comm tallFive wideFive] using h
    exact short_first_normal_form_of_oriented_partition
      second first witnesses wideFive tallFive tallEight
      hsecondCard hfirstCard hwitnessCard hshortSecond.2.1 hshortSecond.1
      hshortSecond.2.2.1 hwideFiveSub htallFiveSub htallEightSub
      (by
        intro third hthird
        have hshape := hwideFiveShape third hthird
        exact ⟨hshape.2, hshape.1⟩)
      (by
        intro third hthird
        have hshape := htallFiveShape third hthird
        exact ⟨hshape.2, hshape.1⟩)
      (by
        intro third hthird
        have hshape := htallEightShape third hthird
        exact ⟨hshape.2, hshape.1⟩)
      hshortPartition (by
        intro third₁ hthird₁ third₂ hthird₂ hne
        rcases hsideDisjoint third₁ hthird₁ third₂ hthird₂ hne with
          hrows | hcols
        · exact Or.inr hrows
        · exact Or.inl hcols)


end ErdosSzekeres

end
