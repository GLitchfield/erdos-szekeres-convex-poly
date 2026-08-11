module

public import ErdosSzekeres.StructuralChargingCarrierOnlyRectangles567

@[expose] public section

/-!
# Area profiles of carrier-only omission rectangles at state 567

The arguments below are color-free after normalization.  They count the
pairwise-disjoint omission rectangles in the six-by-six carrier product and
exclude the only intermediate arithmetic profile by a rectangle-packing
argument.
-/

namespace ErdosSzekeres

/-- The number of carrier-only witness rectangles having a specified area. -/
def OmissionAreaCount567 {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) (area : ℕ) : ℕ :=
  (witnesses.filter fun third ↦
    (first \ third).card * (second \ third).card = area).card

/-- The five normalized carrier-intersection profiles become the five
oppositely ordered omission-side profiles. -/
theorem IsNormalizedCarrierOnlyWitnessSet567.omission_shape
    {n : ℕ} {χ : TripleColoring n}
    {first second third : Finset (Fin n)}
    (hnormal : IsNormalizedCarrierOnlyWitnessSet567 χ first second third)
    (hfirstCard : first.card = 6)
    (hsecondCard : second.card = 6) :
    (((first \ third).card = 5 ∧ (second \ third).card = 1) ∨
      ((first \ third).card = 4 ∧ (second \ third).card = 2) ∨
      ((first \ third).card = 3 ∧ (second \ third).card = 3) ∨
      ((first \ third).card = 2 ∧ (second \ third).card = 4) ∨
      ((first \ third).card = 1 ∧ (second \ third).card = 5)) := by
  rcases hnormal with
    ⟨_hthirdCard, _hstrong, _hsub, _htwo, _hfirstPos, _hfirstLe,
      _hsecondPos, _hsecondLe, _hsum, hprofile⟩
  rw [Finset.card_sdiff, Finset.card_sdiff, hfirstCard, hsecondCard]
  omega

/-- Universal coverage and pairwise disjointness turn the omission rectangles
into an exact area partition of the six-by-six carrier product. -/
theorem IsCarrierOnlyOmissionRectangleSystem567.omission_area_equations
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem :
      IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6)
    (hsecondCard : second.card = 6) :
    5 * OmissionAreaCount567 first second witnesses 5 +
        8 * OmissionAreaCount567 first second witnesses 8 +
        9 * OmissionAreaCount567 first second witnesses 9 = 36 ∧
      witnesses.card =
        OmissionAreaCount567 first second witnesses 5 +
          OmissionAreaCount567 first second witnesses 8 +
          OmissionAreaCount567 first second witnesses 9 := by
  classical
  let row : Finset (Fin n) → Finset (Fin n) := fun third ↦ first \ third
  let col : Finset (Fin n) → Finset (Fin n) := fun third ↦ second \ third
  let area : Finset (Fin n) → ℕ := fun third ↦ (row third).card * (col third).card
  let rect : Finset (Fin n) → Finset (Fin n × Fin n) :=
    fun third ↦ (row third).product (col third)
  let f5 := witnesses.filter fun third ↦ area third = 5
  let f8 := witnesses.filter fun third ↦ area third = 8
  let f9 := witnesses.filter fun third ↦ area third = 9
  have hpartition : witnesses = (f5 ∪ f8) ∪ f9 := by
    ext third
    simp only [f5, f8, f9, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hthird
      have hshape := (hsystem.1 third hthird).omission_shape hfirstCard hsecondCard
      change
        (((row third).card = 5 ∧ (col third).card = 1) ∨
          ((row third).card = 4 ∧ (col third).card = 2) ∨
          ((row third).card = 3 ∧ (col third).card = 3) ∨
          ((row third).card = 2 ∧ (col third).card = 4) ∨
          ((row third).card = 1 ∧ (col third).card = 5)) at hshape
      rcases hshape with h | h | h | h | h
      · exact Or.inl (Or.inl ⟨hthird, by simp [area, h.1, h.2]⟩)
      · exact Or.inl (Or.inr ⟨hthird, by simp [area, h.1, h.2]⟩)
      · exact Or.inr ⟨hthird, by simp [area, h.1, h.2]⟩
      · exact Or.inl (Or.inr ⟨hthird, by simp [area, h.1, h.2]⟩)
      · exact Or.inl (Or.inl ⟨hthird, by simp [area, h.1, h.2]⟩)
    · rintro ((⟨hthird, _⟩ | ⟨hthird, _⟩) | ⟨hthird, _⟩)
      all_goals exact hthird
  have h58 : Disjoint f5 f8 := by
    apply Finset.disjoint_left.mpr
    intro third hthird5 hthird8
    have h5 := (Finset.mem_filter.mp hthird5).2
    have h8 := (Finset.mem_filter.mp hthird8).2
    omega
  have h59 : Disjoint f5 f9 := by
    apply Finset.disjoint_left.mpr
    intro third hthird5 hthird9
    have h5 := (Finset.mem_filter.mp hthird5).2
    have h9 := (Finset.mem_filter.mp hthird9).2
    omega
  have h89 : Disjoint f8 f9 := by
    apply Finset.disjoint_left.mpr
    intro third hthird8 hthird9
    have h8 := (Finset.mem_filter.mp hthird8).2
    have h9 := (Finset.mem_filter.mp hthird9).2
    omega
  have h589 : Disjoint (f5 ∪ f8) f9 :=
    Finset.disjoint_union_left.mpr ⟨h59, h89⟩
  have hcardPartition : witnesses.card = f5.card + f8.card + f9.card := by
    rw [hpartition, Finset.card_union_of_disjoint h589,
      Finset.card_union_of_disjoint h58]
  have hpairwise :
      (witnesses : Set (Finset (Fin n))).PairwiseDisjoint rect := by
    intro third₁ hthird₁ third₂ hthird₂ hne
    simpa [rect, row, col, CarrierOnlyOmissionRectangle567] using
      hsystem.2.2 third₁ hthird₁ third₂ hthird₂ hne
  have hunion : witnesses.biUnion rect = first.product second := by
    ext pair
    obtain ⟨a, b⟩ := pair
    constructor
    · intro hpair
      obtain ⟨third, _hthird, hmem⟩ := Finset.mem_biUnion.mp hpair
      have hdata := Finset.mem_product.mp hmem
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_sdiff.mp hdata.1).1, (Finset.mem_sdiff.mp hdata.2).1⟩
    · intro hpair
      have hdata := Finset.mem_product.mp hpair
      obtain ⟨third, hthird, homit⟩ :=
        hsystem.2.1 a hdata.1 b hdata.2
      apply Finset.mem_biUnion.mpr
      refine ⟨third, hthird, ?_⟩
      simpa [rect, row, col, CarrierOnlyOmissionRectangle567] using homit
  have hareaSum : (∑ third ∈ witnesses, area third) = 36 := by
    calc
      (∑ third ∈ witnesses, area third) =
          ∑ third ∈ witnesses, (rect third).card := by
        apply Finset.sum_congr rfl
        intro third _hthird
        simp [area, rect, Finset.card_product]
      _ = (witnesses.biUnion rect).card := (Finset.card_biUnion hpairwise).symm
      _ = 36 := by
        simp [hunion, Finset.card_product, hfirstCard, hsecondCard]
  have hsum5 : (∑ third ∈ f5, area third) = f5.card * 5 := by
    calc
      (∑ third ∈ f5, area third) = ∑ _third ∈ f5, 5 := by
        apply Finset.sum_congr rfl
        intro third hthird
        exact (Finset.mem_filter.mp hthird).2
      _ = f5.card * 5 := by simp
  have hsum8 : (∑ third ∈ f8, area third) = f8.card * 8 := by
    calc
      (∑ third ∈ f8, area third) = ∑ _third ∈ f8, 8 := by
        apply Finset.sum_congr rfl
        intro third hthird
        exact (Finset.mem_filter.mp hthird).2
      _ = f8.card * 8 := by simp
  have hsum9 : (∑ third ∈ f9, area third) = f9.card * 9 := by
    calc
      (∑ third ∈ f9, area third) = ∑ _third ∈ f9, 9 := by
        apply Finset.sum_congr rfl
        intro third hthird
        exact (Finset.mem_filter.mp hthird).2
      _ = f9.card * 9 := by simp
  have hweighted : 5 * f5.card + 8 * f8.card + 9 * f9.card = 36 := by
    rw [hpartition, Finset.sum_union h589, Finset.sum_union h58,
      hsum5, hsum8, hsum9] at hareaSum
    omega
  simpa [OmissionAreaCount567, f5, f8, f9, area, row, col] using
    And.intro hweighted hcardPartition

private theorem not_disjoint_of_card_lt_add_of_subset
    {α : Type*} [DecidableEq α] {ambient left right : Finset α}
    (hleft : left ⊆ ambient) (hright : right ⊆ ambient)
    (hcard : ambient.card < left.card + right.card) :
    ¬Disjoint left right := by
  intro hdisjoint
  have hunionSub : left ∪ right ⊆ ambient := Finset.union_subset hleft hright
  have hunionCard : (left ∪ right).card = left.card + right.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hle := Finset.card_le_card hunionSub
  omega

/-- If two balanced rectangles are row-disjoint and fill all six rows, then
two area-five rectangles and one area-eight rectangle cannot also be packed
disjointly.  This is the asymmetric half of the middle-profile obstruction. -/
private theorem middle_profile_row_packing_impossible
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (rows : Finset α) (cols : Finset β) (family : Finset ι)
    (row : ι → Finset α) (col : ι → Finset β)
    {balanced₁ balanced₂ five₁ five₂ eight : ι}
    (hrowsCard : rows.card = 6) (hcolsCard : cols.card = 6)
    (hrowSub : ∀ i, row i ⊆ rows) (hcolSub : ∀ i, col i ⊆ cols)
    (hsideDisjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (row i) (row j) ∨ Disjoint (col i) (col j))
    (hbalanced₁Mem : balanced₁ ∈ family)
    (hbalanced₂Mem : balanced₂ ∈ family)
    (hfive₁Mem : five₁ ∈ family) (hfive₂Mem : five₂ ∈ family)
    (heightMem : eight ∈ family)
    (hfiveNe : five₁ ≠ five₂)
    (hbalanced₁Shape : (row balanced₁).card = 3 ∧ (col balanced₁).card = 3)
    (hbalanced₂Shape : (row balanced₂).card = 3 ∧ (col balanced₂).card = 3)
    (hbalancedRows : Disjoint (row balanced₁) (row balanced₂))
    (hfive₁Shape :
      ((row five₁).card = 5 ∧ (col five₁).card = 1) ∨
        ((row five₁).card = 1 ∧ (col five₁).card = 5))
    (hfive₂Shape :
      ((row five₂).card = 5 ∧ (col five₂).card = 1) ∨
        ((row five₂).card = 1 ∧ (col five₂).card = 5))
    (heightShape :
      ((row eight).card = 4 ∧ (col eight).card = 2) ∨
        ((row eight).card = 2 ∧ (col eight).card = 4)) : False := by
  classical
  have hbalancedUnionSub : row balanced₁ ∪ row balanced₂ ⊆ rows :=
    Finset.union_subset (hrowSub balanced₁) (hrowSub balanced₂)
  have hbalancedUnionCard : (row balanced₁ ∪ row balanced₂).card = 6 := by
    rw [Finset.card_union_of_disjoint hbalancedRows,
      hbalanced₁Shape.1, hbalanced₂Shape.1]
  have hareaBalanced₁ :
      (row balanced₁).card * (col balanced₁).card = 9 := by
    rw [hbalanced₁Shape.1, hbalanced₁Shape.2]
  have hareaBalanced₂ :
      (row balanced₂).card * (col balanced₂).card = 9 := by
    rw [hbalanced₂Shape.1, hbalanced₂Shape.2]
  have force_tall (i : ι) (hi : i ∈ family) (p q : ℕ)
      (hp : 4 ≤ p) (hq : 1 ≤ q) (hpq : p * q ≠ 9)
      (hshape :
        ((row i).card = p ∧ (col i).card = q) ∨
          ((row i).card = q ∧ (col i).card = p)) :
      (row i).card = p ∧ (col i).card = q := by
    rcases hshape with htall | hwide
    · exact htall
    · exfalso
      have hareaI : (row i).card * (col i).card = p * q := by
        rw [hwide.1, hwide.2, Nat.mul_comm]
      have hiNeBalanced₁ : i ≠ balanced₁ := by
        intro heq
        subst i
        exact hpq (hareaI.symm.trans hareaBalanced₁)
      have hiNeBalanced₂ : i ≠ balanced₂ := by
        intro heq
        subst i
        exact hpq (hareaI.symm.trans hareaBalanced₂)
      have hrowI₁ : Disjoint (row i) (row balanced₁) := by
        rcases hsideDisjoint i hi balanced₁ hbalanced₁Mem hiNeBalanced₁ with
          hrow | hcol
        · exact hrow
        · exact (not_disjoint_of_card_lt_add_of_subset
            (hcolSub i) (hcolSub balanced₁) (by
              rw [hcolsCard, hwide.2, hbalanced₁Shape.2]
              omega) hcol).elim
      have hrowI₂ : Disjoint (row i) (row balanced₂) := by
        rcases hsideDisjoint i hi balanced₂ hbalanced₂Mem hiNeBalanced₂ with
          hrow | hcol
        · exact hrow
        · exact (not_disjoint_of_card_lt_add_of_subset
            (hcolSub i) (hcolSub balanced₂) (by
              rw [hcolsCard, hwide.2, hbalanced₂Shape.2]
              omega) hcol).elim
      have hrowIUnion :
          Disjoint (row i) (row balanced₁ ∪ row balanced₂) :=
        Finset.disjoint_union_right.mpr ⟨hrowI₁, hrowI₂⟩
      exact (not_disjoint_of_card_lt_add_of_subset
        (hrowSub i) hbalancedUnionSub (by
          rw [hrowsCard, hwide.1, hbalancedUnionCard]
          omega) hrowIUnion).elim
  have hfive₁Tall := force_tall five₁ hfive₁Mem 5 1 (by omega) (by omega)
    (by norm_num) hfive₁Shape
  have hfive₂Tall := force_tall five₂ hfive₂Mem 5 1 (by omega) (by omega)
    (by norm_num) hfive₂Shape
  have heightTall := force_tall eight heightMem 4 2 (by omega) (by omega)
    (by norm_num) heightShape
  have hareaFive₁ : (row five₁).card * (col five₁).card = 5 := by
    rw [hfive₁Tall.1, hfive₁Tall.2]
  have hareaFive₂ : (row five₂).card * (col five₂).card = 5 := by
    rw [hfive₂Tall.1, hfive₂Tall.2]
  have hareaEight : (row eight).card * (col eight).card = 8 := by
    rw [heightTall.1, heightTall.2]
  have distinct_of_area_ne {i j : ι} {areaI areaJ : ℕ}
      (hi : (row i).card * (col i).card = areaI)
      (hj : (row j).card * (col j).card = areaJ)
      (hareas : areaI ≠ areaJ) : i ≠ j := by
    intro hij
    subst j
    exact hareas (hi.symm.trans hj)
  have col_disjoint_of_row_overlap {i j : ι}
      (hi : i ∈ family) (hj : j ∈ family) (hne : i ≠ j)
      (hoverlap : rows.card < (row i).card + (row j).card) :
      Disjoint (col i) (col j) := by
    rcases hsideDisjoint i hi j hj hne with hrow | hcol
    · exact (not_disjoint_of_card_lt_add_of_subset
        (hrowSub i) (hrowSub j) hoverlap hrow).elim
    · exact hcol
  have hfive₁Five₂Cols : Disjoint (col five₁) (col five₂) :=
    col_disjoint_of_row_overlap hfive₁Mem hfive₂Mem hfiveNe (by
      rw [hrowsCard, hfive₁Tall.1, hfive₂Tall.1]
      omega)
  have hfive₁Eight : five₁ ≠ eight :=
    distinct_of_area_ne hareaFive₁ hareaEight (by omega)
  have hfive₂Eight : five₂ ≠ eight :=
    distinct_of_area_ne hareaFive₂ hareaEight (by omega)
  have hfive₁EightCols : Disjoint (col five₁) (col eight) :=
    col_disjoint_of_row_overlap hfive₁Mem heightMem hfive₁Eight (by
      rw [hrowsCard, hfive₁Tall.1, heightTall.1]
      omega)
  have hfive₂EightCols : Disjoint (col five₂) (col eight) :=
    col_disjoint_of_row_overlap hfive₂Mem heightMem hfive₂Eight (by
      rw [hrowsCard, hfive₂Tall.1, heightTall.1]
      omega)
  have hfive₁Balanced₁ : five₁ ≠ balanced₁ :=
    distinct_of_area_ne hareaFive₁ hareaBalanced₁ (by omega)
  have hfive₂Balanced₁ : five₂ ≠ balanced₁ :=
    distinct_of_area_ne hareaFive₂ hareaBalanced₁ (by omega)
  have heightBalanced₁ : eight ≠ balanced₁ :=
    distinct_of_area_ne hareaEight hareaBalanced₁ (by omega)
  have hfive₁BalancedCols : Disjoint (col five₁) (col balanced₁) :=
    col_disjoint_of_row_overlap hfive₁Mem hbalanced₁Mem hfive₁Balanced₁ (by
      rw [hrowsCard, hfive₁Tall.1, hbalanced₁Shape.1]
      omega)
  have hfive₂BalancedCols : Disjoint (col five₂) (col balanced₁) :=
    col_disjoint_of_row_overlap hfive₂Mem hbalanced₁Mem hfive₂Balanced₁ (by
      rw [hrowsCard, hfive₂Tall.1, hbalanced₁Shape.1]
      omega)
  have heightBalancedCols : Disjoint (col eight) (col balanced₁) :=
    col_disjoint_of_row_overlap heightMem hbalanced₁Mem heightBalanced₁ (by
      rw [hrowsCard, heightTall.1, hbalanced₁Shape.1]
      omega)
  have hsmallColsDisjoint :
      Disjoint (col five₁ ∪ col five₂) (col eight) :=
    Finset.disjoint_union_left.mpr ⟨hfive₁EightCols, hfive₂EightCols⟩
  have hsmallColsCard :
      ((col five₁ ∪ col five₂) ∪ col eight).card = 4 := by
    rw [Finset.card_union_of_disjoint hsmallColsDisjoint,
      Finset.card_union_of_disjoint hfive₁Five₂Cols,
      hfive₁Tall.2, hfive₂Tall.2, heightTall.2]
  have small_col_subset_complement (i : ι)
      (hdisjoint : Disjoint (col i) (col balanced₁)) :
      col i ⊆ cols \ col balanced₁ := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hcolSub i hx, fun hxBalanced ↦
        Finset.disjoint_left.mp hdisjoint hx hxBalanced⟩
  have hsmallColsSub :
      (col five₁ ∪ col five₂) ∪ col eight ⊆ cols \ col balanced₁ := by
    apply Finset.union_subset
    · exact Finset.union_subset
        (small_col_subset_complement five₁ hfive₁BalancedCols)
        (small_col_subset_complement five₂ hfive₂BalancedCols)
    · exact small_col_subset_complement eight heightBalancedCols
  have hcomplementCard : (cols \ col balanced₁).card = 3 := by
    rw [Finset.card_sdiff_of_subset (hcolSub balanced₁),
      hcolsCard, hbalanced₁Shape.2]
  have hle := Finset.card_le_card hsmallColsSub
  rw [hsmallColsCard, hcomplementCard] at hle
  omega

/-- The arithmetic middle profile cannot be realized by pairwise-disjoint
rectangles inside two six-element universes. -/
private theorem middle_profile_packing_impossible
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (rows : Finset α) (cols : Finset β) (family : Finset ι)
    (row : ι → Finset α) (col : ι → Finset β)
    (hrowsCard : rows.card = 6) (hcolsCard : cols.card = 6)
    (hrowSub : ∀ i, row i ⊆ rows) (hcolSub : ∀ i, col i ⊆ cols)
    (hshape : ∀ i ∈ family,
      (((row i).card = 5 ∧ (col i).card = 1) ∨
        ((row i).card = 4 ∧ (col i).card = 2) ∨
        ((row i).card = 3 ∧ (col i).card = 3) ∨
        ((row i).card = 2 ∧ (col i).card = 4) ∨
        ((row i).card = 1 ∧ (col i).card = 5)))
    (hsideDisjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
      Disjoint (row i) (row j) ∨ Disjoint (col i) (col j))
    (hfive : (family.filter fun i ↦ (row i).card * (col i).card = 5).card = 2)
    (height : (family.filter fun i ↦ (row i).card * (col i).card = 8).card = 1)
    (hnine : (family.filter fun i ↦ (row i).card * (col i).card = 9).card = 2) : False := by
  classical
  let fiveFamily := family.filter fun i ↦ (row i).card * (col i).card = 5
  let eightFamily := family.filter fun i ↦ (row i).card * (col i).card = 8
  let nineFamily := family.filter fun i ↦ (row i).card * (col i).card = 9
  have hfiveCard : fiveFamily.card = 2 := by simpa [fiveFamily] using hfive
  have heightCard : eightFamily.card = 1 := by simpa [eightFamily] using height
  have hnineCard : nineFamily.card = 2 := by simpa [nineFamily] using hnine
  obtain ⟨five₁, five₂, hfiveNe, hfiveEq⟩ := Finset.card_eq_two.mp hfiveCard
  obtain ⟨eight, heightEq⟩ := Finset.card_eq_one.mp heightCard
  obtain ⟨balanced₁, balanced₂, hbalancedNe, hnineEq⟩ :=
    Finset.card_eq_two.mp hnineCard
  have hfive₁Filter : five₁ ∈ fiveFamily := by rw [hfiveEq]; simp
  have hfive₂Filter : five₂ ∈ fiveFamily := by rw [hfiveEq]; simp
  have heightFilter : eight ∈ eightFamily := by rw [heightEq]; simp
  have hbalanced₁Filter : balanced₁ ∈ nineFamily := by rw [hnineEq]; simp
  have hbalanced₂Filter : balanced₂ ∈ nineFamily := by rw [hnineEq]; simp
  have hfive₁Data : five₁ ∈ family ∧
      (row five₁).card * (col five₁).card = 5 := by
    simpa [fiveFamily] using hfive₁Filter
  have hfive₂Data : five₂ ∈ family ∧
      (row five₂).card * (col five₂).card = 5 := by
    simpa [fiveFamily] using hfive₂Filter
  have heightData : eight ∈ family ∧
      (row eight).card * (col eight).card = 8 := by
    simpa [eightFamily] using heightFilter
  have hbalanced₁Data : balanced₁ ∈ family ∧
      (row balanced₁).card * (col balanced₁).card = 9 := by
    simpa [nineFamily] using hbalanced₁Filter
  have hbalanced₂Data : balanced₂ ∈ family ∧
      (row balanced₂).card * (col balanced₂).card = 9 := by
    simpa [nineFamily] using hbalanced₂Filter
  have five_shape (i : ι) (hi : i ∈ family)
      (harea : (row i).card * (col i).card = 5) :
      ((row i).card = 5 ∧ (col i).card = 1) ∨
        ((row i).card = 1 ∧ (col i).card = 5) := by
    rcases hshape i hi with h | h | h | h | h
    · exact Or.inl h
    · rw [h.1, h.2] at harea
      norm_num at harea
    · rw [h.1, h.2] at harea
      norm_num at harea
    · rw [h.1, h.2] at harea
      norm_num at harea
    · exact Or.inr h
  have eight_shape (i : ι) (hi : i ∈ family)
      (harea : (row i).card * (col i).card = 8) :
      ((row i).card = 4 ∧ (col i).card = 2) ∨
        ((row i).card = 2 ∧ (col i).card = 4) := by
    rcases hshape i hi with h | h | h | h | h
    · rw [h.1, h.2] at harea
      norm_num at harea
    · exact Or.inl h
    · rw [h.1, h.2] at harea
      norm_num at harea
    · exact Or.inr h
    · rw [h.1, h.2] at harea
      norm_num at harea
  have nine_shape (i : ι) (hi : i ∈ family)
      (harea : (row i).card * (col i).card = 9) :
      (row i).card = 3 ∧ (col i).card = 3 := by
    rcases hshape i hi with h | h | h | h | h
    · rw [h.1, h.2] at harea
      norm_num at harea
    · rw [h.1, h.2] at harea
      norm_num at harea
    · exact h
    · rw [h.1, h.2] at harea
      norm_num at harea
    · rw [h.1, h.2] at harea
      norm_num at harea
  have hfive₁Shape := five_shape five₁ hfive₁Data.1 hfive₁Data.2
  have hfive₂Shape := five_shape five₂ hfive₂Data.1 hfive₂Data.2
  have heightShape := eight_shape eight heightData.1 heightData.2
  have hbalanced₁Shape := nine_shape balanced₁ hbalanced₁Data.1 hbalanced₁Data.2
  have hbalanced₂Shape := nine_shape balanced₂ hbalanced₂Data.1 hbalanced₂Data.2
  rcases hsideDisjoint balanced₁ hbalanced₁Data.1 balanced₂ hbalanced₂Data.1
      hbalancedNe with hbalancedRows | hbalancedCols
  · exact middle_profile_row_packing_impossible rows cols family row col
      hrowsCard hcolsCard hrowSub hcolSub hsideDisjoint
      hbalanced₁Data.1 hbalanced₂Data.1 hfive₁Data.1 hfive₂Data.1 heightData.1
      hfiveNe hbalanced₁Shape hbalanced₂Shape hbalancedRows
      hfive₁Shape hfive₂Shape heightShape
  · have hswappedSide : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
        Disjoint (col i) (col j) ∨ Disjoint (row i) (row j) := by
      intro i hi j hj hne
      rcases hsideDisjoint i hi j hj hne with hrow | hcol
      · exact Or.inr hrow
      · exact Or.inl hcol
    have hfive₁Swapped :
        ((col five₁).card = 5 ∧ (row five₁).card = 1) ∨
          ((col five₁).card = 1 ∧ (row five₁).card = 5) := by
      rcases hfive₁Shape with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    have hfive₂Swapped :
        ((col five₂).card = 5 ∧ (row five₂).card = 1) ∨
          ((col five₂).card = 1 ∧ (row five₂).card = 5) := by
      rcases hfive₂Shape with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    have heightSwapped :
        ((col eight).card = 4 ∧ (row eight).card = 2) ∨
          ((col eight).card = 2 ∧ (row eight).card = 4) := by
      rcases heightShape with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    exact middle_profile_row_packing_impossible cols rows family col row
      hcolsCard hrowsCard hcolSub hrowSub hswappedSide
      hbalanced₁Data.1 hbalanced₂Data.1 hfive₁Data.1 hfive₂Data.1 heightData.1
      hfiveNe ⟨hbalanced₁Shape.2, hbalanced₁Shape.1⟩
      ⟨hbalanced₂Shape.2, hbalanced₂Shape.1⟩ hbalancedCols
      hfive₁Swapped hfive₂Swapped heightSwapped

private theorem omission_area_arithmetic_trichotomy
    {n5 n8 n9 : ℕ} (harea : 5 * n5 + 8 * n8 + 9 * n9 = 36) :
    (n5 = 0 ∧ n8 = 0 ∧ n9 = 4) ∨
      (n5 = 2 ∧ n8 = 1 ∧ n9 = 2) ∨
      (n5 = 4 ∧ n8 = 2 ∧ n9 = 0) := by
  have hn8 : n8 ≤ 4 := by omega
  have hn9 : n9 ≤ 4 := by omega
  interval_cases n9 <;> interval_cases n8 <;> omega

/-- A carrier-only omission-rectangle system on two six-element carriers has
exactly one of the two realizable area profiles. -/
theorem IsCarrierOnlyOmissionRectangleSystem567.area_profile_dichotomy
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem :
      IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6)
    (hsecondCard : second.card = 6) :
    (OmissionAreaCount567 first second witnesses 5 = 0 ∧
      OmissionAreaCount567 first second witnesses 8 = 0 ∧
      OmissionAreaCount567 first second witnesses 9 = 4 ∧
      witnesses.card = 4) ∨
    (OmissionAreaCount567 first second witnesses 5 = 4 ∧
      OmissionAreaCount567 first second witnesses 8 = 2 ∧
      OmissionAreaCount567 first second witnesses 9 = 0 ∧
      witnesses.card = 6) := by
  classical
  let n5 := OmissionAreaCount567 first second witnesses 5
  let n8 := OmissionAreaCount567 first second witnesses 8
  let n9 := OmissionAreaCount567 first second witnesses 9
  have hequations := hsystem.omission_area_equations hfirstCard hsecondCard
  have harea : 5 * n5 + 8 * n8 + 9 * n9 = 36 := by
    simpa [n5, n8, n9] using hequations.1
  have hfamilyCard : witnesses.card = n5 + n8 + n9 := by
    simpa [n5, n8, n9] using hequations.2
  rcases omission_area_arithmetic_trichotomy harea with hbalanced | hmiddle | hsplit
  · left
    simpa [n5, n8, n9] using
      And.intro hbalanced.1
        (And.intro hbalanced.2.1
          (And.intro hbalanced.2.2 (show witnesses.card = 4 by omega)))
  · exfalso
    apply middle_profile_packing_impossible first second witnesses
      (fun third ↦ first \ third) (fun third ↦ second \ third)
      hfirstCard hsecondCard
    · intro third
      exact Finset.sdiff_subset
    · intro third
      exact Finset.sdiff_subset
    · intro third hthird
      exact (hsystem.1 third hthird).omission_shape hfirstCard hsecondCard
    · intro third₁ hthird₁ third₂ hthird₂ hne
      apply Finset.disjoint_product.mp
      simpa [CarrierOnlyOmissionRectangle567] using
        hsystem.2.2 third₁ hthird₁ third₂ hthird₂ hne
    · simpa [n5, OmissionAreaCount567] using hmiddle.1
    · simpa [n8, OmissionAreaCount567] using hmiddle.2.1
    · simpa [n9, OmissionAreaCount567] using hmiddle.2.2
  · right
    simpa [n5, n8, n9] using
      And.intro hsplit.1
        (And.intro hsplit.2.1
          (And.intro hsplit.2.2 (show witnesses.card = 6 by omega)))

/-- Four pairwise-disjoint three-by-three omission rectangles covering the
full carrier product. -/
def IsFourDisjointThreeByThreeOmissionGrid567 {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) : Prop :=
  witnesses.card = 4 ∧
    (∀ third ∈ witnesses,
      (first \ third).card = 3 ∧ (second \ third).card = 3) ∧
    (∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses, third₁ ≠ third₂ →
      Disjoint (CarrierOnlyOmissionRectangle567 first second third₁)
        (CarrierOnlyOmissionRectangle567 first second third₂)) ∧
    witnesses.biUnion
        (CarrierOnlyOmissionRectangle567 first second) =
      first.product second

/-- The balanced area profile exposes the omission system as a four-cell
three-by-three grid decomposition. -/
theorem IsCarrierOnlyOmissionRectangleSystem567.fourGrid_of_balanced_area_profile
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem :
      IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6)
    (hsecondCard : second.card = 6)
    (hbalanced :
      OmissionAreaCount567 first second witnesses 5 = 0 ∧
      OmissionAreaCount567 first second witnesses 8 = 0 ∧
      OmissionAreaCount567 first second witnesses 9 = 4 ∧
      witnesses.card = 4) :
    IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses := by
  classical
  have hshape (third : Finset (Fin n)) (hthird : third ∈ witnesses) :
      (first \ third).card = 3 ∧ (second \ third).card = 3 := by
    have hnotFive :
        (first \ third).card * (second \ third).card ≠ 5 := by
      intro harea
      have hmem : third ∈ witnesses.filter (fun candidate ↦
          (first \ candidate).card * (second \ candidate).card = 5) :=
        Finset.mem_filter.mpr ⟨hthird, harea⟩
      have hpositive := Finset.card_pos.mpr ⟨third, hmem⟩
      have hzero : (witnesses.filter (fun candidate ↦
          (first \ candidate).card * (second \ candidate).card = 5)).card = 0 := by
        simpa [OmissionAreaCount567] using hbalanced.1
      exact (Nat.ne_of_gt hpositive) hzero
    have hnotEight :
        (first \ third).card * (second \ third).card ≠ 8 := by
      intro harea
      have hmem : third ∈ witnesses.filter (fun candidate ↦
          (first \ candidate).card * (second \ candidate).card = 8) :=
        Finset.mem_filter.mpr ⟨hthird, harea⟩
      have hpositive := Finset.card_pos.mpr ⟨third, hmem⟩
      have hzero : (witnesses.filter (fun candidate ↦
          (first \ candidate).card * (second \ candidate).card = 8)).card = 0 := by
        simpa [OmissionAreaCount567] using hbalanced.2.1
      exact (Nat.ne_of_gt hpositive) hzero
    rcases (hsystem.1 third hthird).omission_shape hfirstCard hsecondCard with
      h | h | h | h | h
    · exact (hnotFive (by rw [h.1, h.2])).elim
    · exact (hnotEight (by rw [h.1, h.2])).elim
    · exact h
    · exact (hnotEight (by rw [h.1, h.2])).elim
    · exact (hnotFive (by rw [h.1, h.2])).elim
  have hunion : witnesses.biUnion
      (CarrierOnlyOmissionRectangle567 first second) = first.product second := by
    ext pair
    obtain ⟨a, b⟩ := pair
    constructor
    · intro hpair
      obtain ⟨third, _hthird, hmem⟩ := Finset.mem_biUnion.mp hpair
      have hdata := Finset.mem_product.mp hmem
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_sdiff.mp hdata.1).1, (Finset.mem_sdiff.mp hdata.2).1⟩
    · intro hpair
      have hdata := Finset.mem_product.mp hpair
      obtain ⟨third, hthird, homit⟩ := hsystem.2.1 a hdata.1 b hdata.2
      exact Finset.mem_biUnion.mpr ⟨third, hthird, homit⟩
  exact ⟨hbalanced.2.2.2, hshape, hsystem.2.2, hunion⟩

end ErdosSzekeres

end
