module

public import ErdosSzekeres.StructuralChargingNextState578PrivateCupStar

@[expose] public section

/-!
# Boundary exchange infrastructure for the state-578 private-cup ledger

This file isolates the numerical and set-cover parts of the boundary-exchange
route.  The three selected four-cups are pairwise disjoint.  We retain every
selected cup contained in the minimum cup transversal, rather than choosing
only one of them.
-/

namespace ErdosSzekeres

/-- The finite family of the three selected four-cups. -/
def ThreeDisjointCupCapFourPacking578.selectedCups
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    Finset (Finset (Fin n)) :=
  {packing.cup₁, packing.cup₂, packing.cup₃}

/-- The selected cups lying wholly in a proposed transversal. -/
def ThreeDisjointCupCapFourPacking578.fullCupSpines
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (transversal : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  packing.selectedCups.filter fun cup ↦ cup ⊆ transversal

/-- The union of all selected cups lying wholly in the transversal. -/
def ThreeDisjointCupCapFourPacking578.fullCupProtected
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (transversal : Finset (Fin n)) : Finset (Fin n) :=
  (packing.fullCupSpines transversal).biUnion id

/-- The three selected cups form a pairwise-disjoint finite family. -/
theorem ThreeDisjointCupCapFourPacking578.selectedCups_pairwiseDisjoint
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    ((↑packing.selectedCups : Set (Finset (Fin n))).PairwiseDisjoint id) := by
  intro a ha b hb hab
  have ha' : a = packing.cup₁ ∨ a = packing.cup₂ ∨ a = packing.cup₃ := by
    simpa [ThreeDisjointCupCapFourPacking578.selectedCups] using ha
  have hb' : b = packing.cup₁ ∨ b = packing.cup₂ ∨ b = packing.cup₃ := by
    simpa [ThreeDisjointCupCapFourPacking578.selectedCups] using hb
  rcases ha' with ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' <;>
    subst a <;> subst b
  · exact (hab rfl).elim
  · exact packing.cup₁_cup₂
  · exact packing.cup₁_cup₃
  · exact packing.cup₁_cup₂.symm
  · exact (hab rfl).elim
  · exact packing.cup₂_cup₃
  · exact packing.cup₁_cup₃.symm
  · exact packing.cup₂_cup₃.symm
  · exact (hab rfl).elim

/-- Every member of the selected-cup family has four vertices. -/
theorem ThreeDisjointCupCapFourPacking578.selectedCup_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    {cup : Finset (Fin n)} (hcup : cup ∈ packing.selectedCups) :
    cup.card = 4 := by
  have h : cup = packing.cup₁ ∨ cup = packing.cup₂ ∨ cup = packing.cup₃ := by
    simpa [ThreeDisjointCupCapFourPacking578.selectedCups] using hcup
  rcases h with rfl | rfl | rfl
  · exact (mem_capWitnesses.mp packing.cup₁_mem).2.1
  · exact (mem_capWitnesses.mp packing.cup₂_mem).2.1
  · exact (mem_capWitnesses.mp packing.cup₃_mem).2.1

/-- The finite family really has three distinct members. -/
theorem ThreeDisjointCupCapFourPacking578.selectedCups_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.selectedCups.card = 3 := by
  have h₁ : packing.cup₁ ≠ ∅ := by
    intro h
    have hc := (mem_capWitnesses.mp packing.cup₁_mem).2.1
    rw [h] at hc
    simp at hc
  have h₂ : packing.cup₂ ≠ ∅ := by
    intro h
    have hc := (mem_capWitnesses.mp packing.cup₂_mem).2.1
    rw [h] at hc
    simp at hc
  have h₁₂ : packing.cup₁ ≠ packing.cup₂ := packing.cup₁_cup₂.ne h₁
  have h₁₃ : packing.cup₁ ≠ packing.cup₃ := packing.cup₁_cup₃.ne h₁
  have h₂₃ : packing.cup₂ ≠ packing.cup₃ := packing.cup₂_cup₃.ne h₂
  simp [ThreeDisjointCupCapFourPacking578.selectedCups, h₁₂, h₁₃, h₂₃]

/-- The full selected cups remain pairwise disjoint. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupSpines_pairwiseDisjoint
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    ((↑(packing.fullCupSpines transversal) : Set (Finset (Fin n))).PairwiseDisjoint id) := by
  intro a ha b hb hab
  apply packing.selectedCups_pairwiseDisjoint
  · exact Finset.filter_subset _ _ ha
  · exact Finset.filter_subset _ _ hb
  · exact hab

/-- The protected union is contained in the original transversal. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupProtected_subset
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.fullCupProtected transversal ⊆ transversal := by
  rw [ThreeDisjointCupCapFourPacking578.fullCupProtected,
    Finset.biUnion_subset_iff_forall_subset]
  intro cup hcup
  exact (Finset.mem_filter.mp hcup).2

/-- If there are `r` full selected cups, their protected union has exactly
`4 * r` vertices. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupProtected_card
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    (packing.fullCupProtected transversal).card =
      4 * (packing.fullCupSpines transversal).card := by
  rw [ThreeDisjointCupCapFourPacking578.fullCupProtected,
    Finset.card_biUnion packing.fullCupSpines_pairwiseDisjoint]
  simp only [id]
  have hsum : (∑ cup ∈ packing.fullCupSpines transversal, cup.card) =
      (packing.fullCupSpines transversal).card * 4 := by
    apply Finset.sum_const_nat
    intro cup hcup
    exact packing.selectedCup_card (Finset.filter_subset _ _ hcup)
  rw [hsum]
  omega

/-- A proper subset of a four-set has at most three vertices. -/
theorem card_inter_le_three_of_card_eq_four_of_not_subset
    {α : Type*} [DecidableEq α] {transversal cup : Finset α}
    (hcard : cup.card = 4) (hnot : ¬cup ⊆ transversal) :
    (transversal ∩ cup).card ≤ 3 := by
  by_contra hlarge
  have hfour : 4 ≤ (transversal ∩ cup).card := by omega
  have heq : transversal ∩ cup = cup :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  apply hnot
  rw [← heq]
  exact Finset.inter_subset_left

/-- The number of full selected cups is the sum of the three membership
indicators. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupSpines_card_eq
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    (packing.fullCupSpines transversal).card =
      (if packing.cup₁ ⊆ transversal then 1 else 0) +
      (if packing.cup₂ ⊆ transversal then 1 else 0) +
      (if packing.cup₃ ⊆ transversal then 1 else 0) := by
  have h₁ : packing.cup₁ ≠ ∅ := by
    intro h
    have hc := (mem_capWitnesses.mp packing.cup₁_mem).2.1
    rw [h] at hc
    simp at hc
  have h₂ : packing.cup₂ ≠ ∅ := by
    intro h
    have hc := (mem_capWitnesses.mp packing.cup₂_mem).2.1
    rw [h] at hc
    simp at hc
  have h₁₂ : packing.cup₁ ≠ packing.cup₂ := packing.cup₁_cup₂.ne h₁
  have h₁₃ : packing.cup₁ ≠ packing.cup₃ := packing.cup₁_cup₃.ne h₁
  have h₂₃ : packing.cup₂ ≠ packing.cup₃ := packing.cup₂_cup₃.ne h₂
  by_cases h₁Full : packing.cup₁ ⊆ transversal <;>
    by_cases h₂Full : packing.cup₂ ⊆ transversal <;>
    by_cases h₃Full : packing.cup₃ ⊆ transversal <;>
    simp only [ThreeDisjointCupCapFourPacking578.fullCupSpines,
      ThreeDisjointCupCapFourPacking578.selectedCups,
      Finset.filter_insert, Finset.filter_singleton,
      h₁Full, h₂Full, h₃Full, if_pos] <;>
    simp [h₁₂, h₁₃, h₂₃]

/-- At least ten selected vertices force at least one full selected cup. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupSpines_nonempty_of_ten_le
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (hsub : transversal ⊆ packing.cupSupport)
    (hten : 10 ≤ transversal.card) :
    (packing.fullCupSpines transversal).Nonempty := by
  rcases packing.exists_cup_subset_of_ten_le hsub hten with h₁ | h₂ | h₃
  · exact ⟨packing.cup₁, by simp [ThreeDisjointCupCapFourPacking578.fullCupSpines,
      ThreeDisjointCupCapFourPacking578.selectedCups, h₁]⟩
  · exact ⟨packing.cup₂, by simp [ThreeDisjointCupCapFourPacking578.fullCupSpines,
      ThreeDisjointCupCapFourPacking578.selectedCups, h₂]⟩
  · exact ⟨packing.cup₃, by simp [ThreeDisjointCupCapFourPacking578.fullCupSpines,
      ThreeDisjointCupCapFourPacking578.selectedCups, h₃]⟩

/-- There are at most three full selected cups. -/
theorem ThreeDisjointCupCapFourPacking578.fullCupSpines_card_le_three
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    (packing.fullCupSpines transversal).card ≤ 3 := by
  have hle := Finset.card_le_card
    (Finset.filter_subset (fun cup ↦ cup ⊆ transversal) packing.selectedCups)
  rw [packing.selectedCups_card] at hle
  exact hle

/-- If `r` selected cups lie wholly in the transversal, then the transversal
has at most `9 + r` vertices. -/
theorem ThreeDisjointCupCapFourPacking578.transversal_card_le_nine_add_fullCupSpines
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (hsub : transversal ⊆ packing.cupSupport) :
    transversal.card ≤ 9 + (packing.fullCupSpines transversal).card := by
  have hcup₁Card := (mem_capWitnesses.mp packing.cup₁_mem).2.1
  have hcup₂Card := (mem_capWitnesses.mp packing.cup₂_mem).2.1
  have hcup₃Card := (mem_capWitnesses.mp packing.cup₃_mem).2.1
  have h₁ : (transversal ∩ packing.cup₁).card ≤
      if packing.cup₁ ⊆ transversal then 4 else 3 := by
    by_cases hfull : packing.cup₁ ⊆ transversal
    · rw [if_pos hfull, Finset.inter_eq_right.mpr hfull, hcup₁Card]
    · simpa [hfull] using
        card_inter_le_three_of_card_eq_four_of_not_subset hcup₁Card hfull
  have h₂ : (transversal ∩ packing.cup₂).card ≤
      if packing.cup₂ ⊆ transversal then 4 else 3 := by
    by_cases hfull : packing.cup₂ ⊆ transversal
    · rw [if_pos hfull, Finset.inter_eq_right.mpr hfull, hcup₂Card]
    · simpa [hfull] using
        card_inter_le_three_of_card_eq_four_of_not_subset hcup₂Card hfull
  have h₃ : (transversal ∩ packing.cup₃).card ≤
      if packing.cup₃ ⊆ transversal then 4 else 3 := by
    by_cases hfull : packing.cup₃ ⊆ transversal
    · rw [if_pos hfull, Finset.inter_eq_right.mpr hfull, hcup₃Card]
    · simpa [hfull] using
        card_inter_le_three_of_card_eq_four_of_not_subset hcup₃Card hfull
  have hdecomp : transversal =
      (transversal ∩ packing.cup₁) ∪
        (transversal ∩ packing.cup₂) ∪
          (transversal ∩ packing.cup₃) := by
    ext x
    constructor
    · intro hx
      have hxSupport := hsub hx
      simp only [ThreeDisjointCupCapFourPacking578.cupSupport,
        Finset.mem_union, Finset.mem_inter] at hxSupport ⊢
      rcases hxSupport with (hx₁ | hx₂) | hx₃
      · exact Or.inl (Or.inl ⟨hx, hx₁⟩)
      · exact Or.inl (Or.inr ⟨hx, hx₂⟩)
      · exact Or.inr ⟨hx, hx₃⟩
    · simp only [Finset.mem_union, Finset.mem_inter]
      rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have h₁₂ : Disjoint (transversal ∩ packing.cup₁)
      (transversal ∩ packing.cup₂) :=
    packing.cup₁_cup₂.mono Finset.inter_subset_right Finset.inter_subset_right
  have h₁₃ : Disjoint (transversal ∩ packing.cup₁)
      (transversal ∩ packing.cup₃) :=
    packing.cup₁_cup₃.mono Finset.inter_subset_right Finset.inter_subset_right
  have h₂₃ : Disjoint (transversal ∩ packing.cup₂)
      (transversal ∩ packing.cup₃) :=
    packing.cup₂_cup₃.mono Finset.inter_subset_right Finset.inter_subset_right
  have hleftRight : Disjoint
      ((transversal ∩ packing.cup₁) ∪ (transversal ∩ packing.cup₂))
      (transversal ∩ packing.cup₃) :=
    Finset.disjoint_union_left.mpr ⟨h₁₃, h₂₃⟩
  have hcardEq : transversal.card =
      (transversal ∩ packing.cup₁).card +
        (transversal ∩ packing.cup₂).card +
          (transversal ∩ packing.cup₃).card := by
    have heq := congrArg Finset.card hdecomp
    rw [Finset.card_union_of_disjoint hleftRight,
      Finset.card_union_of_disjoint h₁₂] at heq
    exact heq
  rw [packing.fullCupSpines_card_eq]
  by_cases h₁Full : packing.cup₁ ⊆ transversal <;>
    by_cases h₂Full : packing.cup₂ ⊆ transversal <;>
    by_cases h₃Full : packing.cup₃ ⊆ transversal <;>
    simp [h₁Full, h₂Full, h₃Full] at h₁ h₂ h₃ ⊢ <;>
    omega

/-- The four-cups missed by the part of the ledger transversal outside a
protected set. -/
noncomputable def PrivateCupLedger578.residualCupFamily
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (protectedSet : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (capWitnesses χ.dual support 4).filter fun cup ↦
    Disjoint cup (ledger.transversal \ protectedSet)

/-- Membership in the residual family exposes exactly the witness and
disjointness conditions used by the boundary-exchange contract. -/
theorem PrivateCupLedger578.mem_residualCupFamily
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    {protectedSet cup : Finset (Fin n)} :
    cup ∈ ledger.residualCupFamily protectedSet ↔
      cup ∈ capWitnesses χ.dual support 4 ∧
        Disjoint cup (ledger.transversal \ protectedSet) := by
  simp [PrivateCupLedger578.residualCupFamily]

/-- Hitting the filtered residual family is equivalent to the universal
`hits` premise of the boundary-exchange theorem. -/
theorem PrivateCupLedger578.hits_residualCupFamily_iff
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    {protectedSet boundary : Finset (Fin n)} :
    (∀ cup, cup ∈ ledger.residualCupFamily protectedSet →
        ¬Disjoint cup boundary) ↔
      ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
        Disjoint cup (ledger.transversal \ protectedSet) →
          ¬Disjoint cup boundary := by
  constructor
  · intro hhits cup hcup hdisjoint
    exact hhits cup (ledger.mem_residualCupFamily.mpr ⟨hcup, hdisjoint⟩)
  · intro hhits cup hcup
    exact hhits cup (ledger.mem_residualCupFamily.mp hcup).1
      (ledger.mem_residualCupFamily.mp hcup).2

/-- The exact remaining positive datum after the full-spine arithmetic has
been discharged: a boundary of size at most three per full selected cup which
hits every residual cup. -/
structure FullSpineResidualBoundary578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  boundary : Finset (Fin n)
  boundary_sub : boundary ⊆ support
  boundary_card : boundary.card ≤
    3 * (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card
  hits : ∀ cup,
    cup ∈ joint.ledger.residualCupFamily
      (joint.saturation.state.packing.fullCupProtected
        joint.ledger.transversal) →
      ¬Disjoint cup boundary

/-- A residual boundary fills every field of the previously compiled
boundary-exchange interface. -/
noncomputable def FullSpineResidualBoundary578.toPrivateCupBoundaryExchange
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (residual : FullSpineResidualBoundary578 joint) :
    PrivateCupBoundaryExchange578 joint := by
  let packing := joint.saturation.state.packing
  let fullSpines := packing.fullCupSpines joint.ledger.transversal
  let protectedSet := packing.fullCupProtected joint.ledger.transversal
  refine {
    r := fullSpines.card
    protectedSet := protectedSet
    boundary := residual.boundary
    protectedSet_sub := ?_
    protectedSet_card := ?_
    enough := ?_
    boundary_sub := residual.boundary_sub
    boundary_card := ?_
    hits := ?_
  }
  · exact packing.fullCupProtected_subset
  · exact packing.fullCupProtected_card
  · exact packing.transversal_card_le_nine_add_fullCupSpines
      joint.ledger.transversal_sub
  · exact residual.boundary_card
  · intro cup hcup hdisjoint
    exact residual.hits cup
      (joint.ledger.mem_residualCupFamily.mpr ⟨hcup, hdisjoint⟩)

/-- The canonical full-spine family in a private-cup ledger is nonempty. -/
theorem PrivateCupStarSixCapState578.fullCupSpines_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) :
    (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).Nonempty :=
  joint.saturation.state.packing.fullCupSpines_nonempty_of_ten_le
    joint.ledger.transversal_sub joint.ledger.ten_le

/-! ## The collective address-matrix invariant -/

/-- Of two prefix-comparable lists, the shorter one is a prefix of the
longer one. -/
theorem listPrefix_of_length_le_of_comparable
    {α : Type*} {a b : List α}
    (hlen : a.length ≤ b.length)
    (hcomp : a <+: b ∨ b <+: a) :
    a <+: b := by
  rcases hcomp with hab | hba
  · exact hab
  · have heq : b.length = a.length := Nat.le_antisymm hba.length_le hlen
    have hbaEq : b = a := hba.eq_of_length heq
    simp [hbaEq]

/-- The row/column chain argument is purely combinatorial and applies to any
`4 × 6` matrix of list addresses. -/
theorem exists_globalPrefixMinimum_fourBySix
    (path : Fin 4 → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j) :
    ∃ i₀ j₀, ∀ i j, path i₀ j₀ <+: path i j := by
  classical
  obtain ⟨cell, _hcell, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Fin 4)).product (Finset.univ : Finset (Fin 6)))
    (fun p ↦ (path p.1 p.2).length) (by simp)
  refine ⟨cell.1, cell.2, ?_⟩
  intro i j
  have hbaseLe : (path cell.1 cell.2).length ≤ (path i j).length :=
    hmin (i, j) (by simp)
  have hintermediate : path cell.1 cell.2 <+: path i cell.2 :=
    listPrefix_of_length_le_of_comparable
      (hmin (i, cell.2) (by simp)) (hcolumn cell.1 i cell.2)
  rcases hrow i cell.2 j with hforward | hback
  · exact hintermediate.trans hforward
  · exact listPrefix_of_length_le_of_comparable hbaseLe
      (List.prefix_or_prefix_of_prefix hintermediate hback)

/-- A globally minimal cell of the mixed matrix: its joint-split address is a
prefix of every one of the twenty-four addresses. -/
structure PrivateCupSixCapCommonMinimum578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree) where
  row : Fin 4
  column : Fin 6
  minimal : ∀ i j, (matrix.cell row column).path <+: (matrix.cell i j).path

/-- Row and column prefix-comparability force a global minimum in the mixed
`4 × 6` address matrix.  This uses all twenty-four cells collectively; it is
strictly stronger than choosing separate row or column minima. -/
theorem PrivateCupSixCapAddressMatrix578.commonMinimum_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree) :
    Nonempty (PrivateCupSixCapCommonMinimum578 matrix) := by
  classical
  obtain ⟨cell, _hcell, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Fin 4)).product (Finset.univ : Finset (Fin 6)))
    (fun p ↦ (matrix.cell p.1 p.2).path.length) (by simp)
  refine ⟨{ row := cell.1, column := cell.2, minimal := ?_ }⟩
  intro i j
  have hbaseLe : (matrix.cell cell.1 cell.2).path.length ≤
      (matrix.cell i j).path.length := hmin (i, j) (by simp)
  have hintermediate : (matrix.cell cell.1 cell.2).path <+:
      (matrix.cell i cell.2).path :=
    listPrefix_of_length_le_of_comparable
      (hmin (i, cell.2) (by simp))
      (matrix.column_paths_comparable cell.1 i cell.2)
  rcases matrix.row_paths_comparable i cell.2 j with hforward | hback
  · exact hintermediate.trans hforward
  · exact listPrefix_of_length_le_of_comparable hbaseLe
      (List.prefix_or_prefix_of_prefix hintermediate hback)

/-- A canonical choice of global minimum for downstream constructions. -/
noncomputable def PrivateCupSixCapAddressMatrix578.commonMinimum
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree) :
    PrivateCupSixCapCommonMinimum578 matrix :=
  Classical.choice matrix.commonMinimum_nonempty

/-- A path extending `base` and comparable with paths taking opposite first
steps after `base` must equal `base`. -/
theorem list_eq_base_of_opposite_prefix_extensions
    {α : Type*} [DecidableEq α]
    {base path : List α} {left right : α}
    (hne : left ≠ right)
    {leftTail rightTail : List α}
    (hbase : base <+: path)
    (hleft : path <+: base ++ left :: leftTail ∨
      base ++ left :: leftTail <+: path)
    (hright : path <+: base ++ right :: rightTail ∨
      base ++ right :: rightTail <+: path) :
    path = base := by
  rcases hbase with ⟨tail, rfl⟩
  cases tail with
  | nil => simp
  | cons direction rest =>
      have hdLeft : direction = left := by
        rcases hleft with h | h
        · have hd := h.drop base.length
          exact (List.cons_prefix_cons.mp (by simpa using hd)).1
        · have hd := h.drop base.length
          exact (List.cons_prefix_cons.mp (by simpa using hd)).1.symm
      have hdRight : direction = right := by
        rcases hright with h | h
        · have hd := h.drop base.length
          exact (List.cons_prefix_cons.mp (by simpa using hd)).1
        · have hd := h.drop base.length
          exact (List.cons_prefix_cons.mp (by simpa using hd)).1.symm
      exact (hne (hdLeft.symm.trans hdRight)).elim

/-- If two cells leave a common minimum in opposite directions, both cross
corners are exactly the common minimum.  This is the rectangle constraint
behind the bounded `4 × 6` census. -/
theorem PrivateCupSixCapCommonMinimum578.crossCorners_eq_of_oppositeExtensions
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : PrivateCupSixCapAddressMatrix578 joint tree}
    (minimum : PrivateCupSixCapCommonMinimum578 matrix)
    {i k : Fin 4} {j l : Fin 6} {leftTail rightTail : List Bool}
    (hleft : (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: leftTail)
    (hright : (matrix.cell k l).path =
      (matrix.cell minimum.row minimum.column).path ++ true :: rightTail) :
    (matrix.cell i l).path =
        (matrix.cell minimum.row minimum.column).path ∧
      (matrix.cell k j).path =
        (matrix.cell minimum.row minimum.column).path := by
  let base := (matrix.cell minimum.row minimum.column).path
  constructor
  · apply list_eq_base_of_opposite_prefix_extensions
      (base := base) (left := false) (right := true) (by decide)
      (minimum.minimal i l)
    · simpa [base, hleft] using matrix.row_paths_comparable i l j
    · simpa [base, hright] using matrix.column_paths_comparable i k l
  · apply list_eq_base_of_opposite_prefix_extensions
      (base := base) (left := false) (right := true) (by decide)
      (minimum.minimal k j)
    · simpa [base, hleft, or_comm] using matrix.column_paths_comparable i k j
    · simpa [base, hright, or_comm] using matrix.row_paths_comparable k j l

/-- A path is either its known prefix or has a first step after that prefix. -/
theorem list_eq_or_exists_firstStep_of_prefix
    {α : Type*} {base path : List α} (hprefix : base <+: path) :
    path = base ∨ ∃ direction tail, path = base ++ direction :: tail := by
  rcases hprefix with ⟨tail, rfl⟩
  cases tail with
  | nil => simp
  | cons direction rest => exact Or.inr ⟨direction, rest, rfl⟩

/-- If a lowest-separating address next takes the lower edge after a resolved
ancestor address, the whole witness is contained in that ancestor's lower
child. -/
theorem DecompositionTree.IsLowestSeparatingPath.subset_lower_of_path_eq_append_false
    {n : ℕ} {χ : TripleColoring n}
    {support witness : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    {path base tail : List Bool} {node : DecompositionSplit χ}
    (halloc : DecompositionTree.IsLowestSeparatingPath witness tree path)
    (hlookup : tree.splitAtPath base = some node)
    (heq : path = base ++ false :: tail) :
    witness ⊆ node.lower := by
  induction halloc generalizing base node tail with
  | root => simp at heq
  | @lower lower upper lowerTree upperTree deep path hsub hpath ih =>
      cases base with
      | nil =>
          simp only [DecompositionTree.splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact hsub
      | cons direction base =>
          cases direction
          · apply ih (base := base) (tail := tail)
            · simpa [DecompositionTree.splitAtPath] using hlookup
            · simpa using heq
          · simp at heq
  | @upper lower upper lowerTree upperTree deep path hnotLower hsub hpath ih =>
      cases base with
      | nil => simp at heq
      | cons direction base =>
          cases direction
          · simp at heq
          · apply ih (base := base) (tail := tail)
            · simpa [DecompositionTree.splitAtPath] using hlookup
            · simpa using heq

/-- The upper-child analogue of
`subset_lower_of_path_eq_append_false`. -/
theorem DecompositionTree.IsLowestSeparatingPath.subset_upper_of_path_eq_append_true
    {n : ℕ} {χ : TripleColoring n}
    {support witness : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    {path base tail : List Bool} {node : DecompositionSplit χ}
    (halloc : DecompositionTree.IsLowestSeparatingPath witness tree path)
    (hlookup : tree.splitAtPath base = some node)
    (heq : path = base ++ true :: tail) :
    witness ⊆ node.upper := by
  induction halloc generalizing base node tail with
  | root => simp at heq
  | @lower lower upper lowerTree upperTree deep path hsub hpath ih =>
      cases base with
      | nil => simp at heq
      | cons direction base =>
          cases direction
          · apply ih (base := base) (tail := tail)
            · simpa [DecompositionTree.splitAtPath] using hlookup
            · simpa using heq
          · simp at heq
  | @upper lower upper lowerTree upperTree deep path hnotLower hsub hpath ih =>
      cases base with
      | nil =>
          simp only [DecompositionTree.splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact hsub
      | cons direction base =>
          cases direction
          · simp at heq
          · apply ih (base := base) (tail := tail)
            · simpa [DecompositionTree.splitAtPath] using hlookup
            · simpa using heq

/-- A cell is at `base` or descends from it in the named direction. -/
def AddressAtOrExtends578 (base : List Bool) (direction : Bool)
    (path : List Bool) : Prop :=
  path = base ∨ ∃ tail, path = base ++ direction :: tail

/-- Generic cross-corner collapse for a row/column-comparable address
matrix. -/
theorem fourBySix_crossCorners_eq_of_oppositeExtensions
    (path : Fin 4 → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j)
    {i₀ : Fin 4} {j₀ : Fin 6}
    (hminimum : ∀ i j, path i₀ j₀ <+: path i j)
    {i k : Fin 4} {j l : Fin 6} {leftTail rightTail : List Bool}
    (hleft : path i j = path i₀ j₀ ++ false :: leftTail)
    (hright : path k l = path i₀ j₀ ++ true :: rightTail) :
    path i l = path i₀ j₀ ∧ path k j = path i₀ j₀ := by
  let base := path i₀ j₀
  constructor
  · apply list_eq_base_of_opposite_prefix_extensions
      (base := base) (left := false) (right := true) (by decide)
      (hminimum i l)
    · simpa [base, hleft] using hrow i l j
    · simpa [base, hright] using hcolumn i k l
  · apply list_eq_base_of_opposite_prefix_extensions
      (base := base) (left := false) (right := true) (by decide)
      (hminimum k j)
    · simpa [base, hleft, or_comm] using hcolumn i k j
    · simpa [base, hright, or_comm] using hrow k j l

/-- Generic one-sided/mixed trichotomy for any `4 × 6` prefix-chain matrix
with a chosen global minimum. -/
theorem fourBySix_oneSided_or_crossCorners
    (path : Fin 4 → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j)
    {i₀ : Fin 4} {j₀ : Fin 6}
    (hminimum : ∀ i j, path i₀ j₀ <+: path i j) :
    (∀ i j, AddressAtOrExtends578 (path i₀ j₀) false (path i j)) ∨
    (∀ i j, AddressAtOrExtends578 (path i₀ j₀) true (path i j)) ∨
    ∃ i k j l, path i l = path i₀ j₀ ∧ path k j = path i₀ j₀ := by
  let base := path i₀ j₀
  by_cases hleft : ∃ i j tail, path i j = base ++ false :: tail
  · by_cases hright : ∃ k l tail, path k l = base ++ true :: tail
    · rcases hleft with ⟨i, j, leftTail, hleft⟩
      rcases hright with ⟨k, l, rightTail, hright⟩
      exact Or.inr (Or.inr ⟨i, k, j, l,
        fourBySix_crossCorners_eq_of_oppositeExtensions
          path hrow hcolumn hminimum hleft hright⟩)
    · left
      intro i j
      rcases list_eq_or_exists_firstStep_of_prefix (hminimum i j) with
        heq | ⟨direction, tail, hstep⟩
      · exact Or.inl heq
      · cases direction with
        | false => exact Or.inr ⟨tail, by simpa [base] using hstep⟩
        | true => exact (hright ⟨i, j, tail, by simpa [base] using hstep⟩).elim
  · right
    left
    intro i j
    rcases list_eq_or_exists_firstStep_of_prefix (hminimum i j) with
      heq | ⟨direction, tail, hstep⟩
    · exact Or.inl heq
    · cases direction with
      | false => exact (hleft ⟨i, j, tail, by simpa [base] using hstep⟩).elim
      | true => exact Or.inr ⟨tail, by simpa [base] using hstep⟩

/-- The exact collective trichotomy certified by the matrix census.  Below a
global minimum, either every cell is at-or-left, every cell is at-or-right, or
opposite strict directions occur and a cross rectangle collapses back to the
minimum in both other corners. -/
theorem PrivateCupSixCapCommonMinimum578.oneSided_or_crossCorners
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : PrivateCupSixCapAddressMatrix578 joint tree}
    (minimum : PrivateCupSixCapCommonMinimum578 matrix) :
    (∀ i j, AddressAtOrExtends578
      (matrix.cell minimum.row minimum.column).path false
      (matrix.cell i j).path) ∨
    (∀ i j, AddressAtOrExtends578
      (matrix.cell minimum.row minimum.column).path true
      (matrix.cell i j).path) ∨
    ∃ i k j l,
      (matrix.cell i l).path =
          (matrix.cell minimum.row minimum.column).path ∧
        (matrix.cell k j).path =
          (matrix.cell minimum.row minimum.column).path := by
  let base := (matrix.cell minimum.row minimum.column).path
  by_cases hleft : ∃ i j tail,
      (matrix.cell i j).path = base ++ false :: tail
  · by_cases hright : ∃ k l tail,
        (matrix.cell k l).path = base ++ true :: tail
    · rcases hleft with ⟨i, j, leftTail, hleft⟩
      rcases hright with ⟨k, l, rightTail, hright⟩
      exact Or.inr (Or.inr ⟨i, k, j, l,
        minimum.crossCorners_eq_of_oppositeExtensions hleft hright⟩)
    · left
      intro i j
      rcases list_eq_or_exists_firstStep_of_prefix (minimum.minimal i j) with
        heq | ⟨direction, tail, hstep⟩
      · exact Or.inl heq
      · cases direction with
        | false => exact Or.inr ⟨tail, by simpa [base] using hstep⟩
        | true => exact (hright ⟨i, j, tail, by simpa [base] using hstep⟩).elim
  · right
    left
    intro i j
    rcases list_eq_or_exists_firstStep_of_prefix (minimum.minimal i j) with
      heq | ⟨direction, tail, hstep⟩
    · exact Or.inl heq
    · cases direction with
      | false => exact (hleft ⟨i, j, tail, by simpa [base] using hstep⟩).elim
      | true => exact Or.inr ⟨tail, by simpa [base] using hstep⟩

/-- A strict lower extension from the common minimum localizes both witnesses
of that matrix cell inside the minimum node's lower child. -/
theorem PrivateCupSixCapCommonMinimum578.cell_union_subset_lower_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : PrivateCupSixCapAddressMatrix578 joint tree}
    (minimum : PrivateCupSixCapCommonMinimum578 matrix)
    {i : Fin 4} {j : Fin 6} {tail : List Bool}
    (hextends : (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: tail) :
    joint.star.privateCupAt i ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.lower :=
  (matrix.cell i j).allocated.subset_lower_of_path_eq_append_false
    (matrix.cell minimum.row minimum.column).lookup hextends

/-- A strict upper extension has the symmetric localization property. -/
theorem PrivateCupSixCapCommonMinimum578.cell_union_subset_upper_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : PrivateCupSixCapAddressMatrix578 joint tree}
    (minimum : PrivateCupSixCapCommonMinimum578 matrix)
    {i : Fin 4} {j : Fin 6} {tail : List Bool}
    (hextends : (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path ++ true :: tail) :
    joint.star.privateCupAt i ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.upper :=
  (matrix.cell i j).allocated.subset_upper_of_path_eq_append_true
    (matrix.cell minimum.row minimum.column).lookup hextends

/-! ## Tight one-spine exchange and its seven-vertex carrier -/

/-- The `32/23` density can be used in contrapositive form: every proposed
set of at most nine reservoir vertices misses some four-cup. -/
theorem exists_fourCup_disjoint_from_of_card_le_nine_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir candidate : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hcandidateSub : candidate ⊆ reservoir)
    (hcandidateCard : candidate.card ≤ 9) :
    ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
      Disjoint cup candidate := by
  by_contra hnone
  have hhits : ∀ cup, cup ∈ capWitnesses χ.dual reservoir 4 →
      ¬Disjoint cup candidate := by
    intro cup hcup hdisjoint
    exact hnone ⟨cup, hcup, hdisjoint⟩
  have hten := ten_le_fourCupTransversal_of_colorDualLower_at_578
    hreservoir hcard hnoCap hnoStrong
    (show IsCupWitnessTransversal578 χ reservoir candidate 4 from
      ⟨hcandidateSub, hhits⟩)
  omega

/-- A genuinely new residual four-cup forced by a three-vertex partial-tail
exchange.  The proposed boundary consists of its owner and two vertices of
the owner's private tail.  The missed cup avoids that boundary and the
unprotected transversal, hence meets a different spine owner. -/
structure SevenVertexResidualCupCarrier578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  owner : Fin n
  owner_mem : owner ∈ joint.star.spine
  omittedTailVertex : Fin n
  omittedTailVertex_mem : omittedTailVertex ∈
    joint.ledger.tailFor owner
      (joint.star.spine_sub_transversal owner_mem)
  cup : Finset (Fin n)
  cup_mem : cup ∈ capWitnesses χ.dual support 4
  avoids_unprotected :
    Disjoint cup (joint.ledger.transversal \ joint.star.spine)
  avoids_partialBoundary : Disjoint cup
    (insert owner ((joint.ledger.tailFor owner
      (joint.star.spine_sub_transversal owner_mem)).erase omittedTailVertex))
  meets_other_owner : ¬Disjoint cup (joint.star.spine.erase owner)
  cup_ne_spine : cup ≠ joint.star.spine
  carrier_card : (joint.star.spine ∪ cup).card ≤ 7

/-- In the one-full-spine branch the owner transversal is exactly ten
vertices. -/
theorem PrivateCupStarSixCapState578.transversal_card_eq_ten_of_fullCupSpines_card_eq_one
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    joint.ledger.transversal.card = 10 := by
  have hle :=
    joint.saturation.state.packing.transversal_card_le_nine_add_fullCupSpines
      joint.ledger.transversal_sub
  have hten := joint.ledger.ten_le
  rw [hone] at hle
  omega

/-- With only one full selected cup, the canonical protected union is exactly
the star spine. -/
theorem PrivateCupStarSixCapState578.fullCupProtected_eq_spine_of_card_eq_one
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    joint.saturation.state.packing.fullCupProtected
      joint.ledger.transversal = joint.star.spine := by
  classical
  have hselected : joint.star.spine ∈
      joint.saturation.state.packing.selectedCups := by
    rcases joint.star.spine_selected with h | h | h <;>
      simp [ThreeDisjointCupCapFourPacking578.selectedCups, h]
  have hfull : joint.star.spine ∈
      joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal :=
    Finset.mem_filter.mpr ⟨hselected, joint.star.spine_sub_transversal⟩
  obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hone
  have hspineEq : joint.star.spine = only := by
    simpa [honly] using hfull
  rw [ThreeDisjointCupCapFourPacking578.fullCupProtected, honly]
  simp [hspineEq]

/-- Any family of four-subsets on at most six vertices has a transversal of
at most three vertices; no coloring hypothesis is needed. -/
theorem atMostSix_fourCupFamily_has_threeTransversal
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hcard : carrier.card ≤ 6) :
    ∃ transversal : Finset (Fin n),
      transversal ⊆ carrier ∧ transversal.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ carrier transversal 4 := by
  classical
  by_cases hsmall : carrier.card ≤ 3
  · refine ⟨carrier, Finset.Subset.rfl, hsmall, Finset.Subset.rfl, ?_⟩
    intro cup hcup
    have hle := Finset.card_le_card (mem_capWitnesses.mp hcup).1
    rw [(mem_capWitnesses.mp hcup).2.1] at hle
    omega
  · have hthree : 3 ≤ carrier.card := by omega
    obtain ⟨transversal, htransversalSub, htransversalCard⟩ :=
      Finset.exists_subset_card_eq
        (show carrier.card - 3 ≤ carrier.card by omega)
    refine ⟨transversal, htransversalSub, by omega,
      htransversalSub, ?_⟩
    intro cup hcup hdisjoint
    have hcupData := mem_capWitnesses.mp hcup
    have hcupSub : cup ⊆ carrier \ transversal := by
      intro x hxCup
      exact Finset.mem_sdiff.mpr ⟨hcupData.1 hxCup,
        fun hxTransversal ↦
          (Finset.disjoint_left.mp hdisjoint hxCup) hxTransversal⟩
    have hle := Finset.card_le_card hcupSub
    rw [Finset.card_sdiff_of_subset htransversalSub,
      htransversalCard, hcupData.2.1] at hle
    omega

/-- The exact-cardinality seven-vertex theorem extends to every carrier of
cardinality at most seven. -/
theorem atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hcard : carrier.card ≤ 7) :
    ContainsCupSet χ carrier 5 ∨
      ∃ transversal : Finset (Fin n),
        transversal ⊆ carrier ∧ transversal.card ≤ 3 ∧
          IsCupWitnessTransversal578 χ carrier transversal 4 := by
  by_cases heq : carrier.card = 7
  · exact sevenVertex_fourCupFamily_has_threeTransversal_or_cupFive heq
  · exact Or.inr (atMostSix_fourCupFamily_has_threeTransversal (by omega))

/-- Rebase the private-star construction at any selected cup which lies fully
in the owner transversal. -/
def PrivateCupStarSixCapState578.starAtFullSpine
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) : PrivateCupStar578 joint.ledger := by
  have hdata := Finset.mem_filter.mp hspine
  refine {
    spine := spine
    spine_selected := ?_
    spine_sub_transversal := hdata.2
  }
  simpa [ThreeDisjointCupCapFourPacking578.selectedCups] using hdata.1

/-- The canonical seven-vertex carrier attached to one full spine uses its
first owner and that owner's private cup. -/
def PrivateCupStarSixCapState578.carrierAtFullSpine
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) : Finset (Fin n) :=
  let star := joint.starAtFullSpine hspine
  spine ∪ star.privateCupAt (0 : Fin 4)

theorem PrivateCupStarSixCapState578.carrierAtFullSpine_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) :
    (joint.carrierAtFullSpine hspine).card = 7 := by
  classical
  let star := joint.starAtFullSpine hspine
  have hspineEq : star.spine = spine := rfl
  have hspineCard : spine.card = 4 := by
    have hselected := (Finset.mem_filter.mp hspine).1
    exact joint.saturation.state.packing.selectedCup_card hselected
  have hprivateCard : (star.privateCupAt (0 : Fin 4)).card = 4 :=
    (mem_capWitnesses.mp (star.privateCupAt_mem (0 : Fin 4))).2.1
  have hinter : spine ∩ star.privateCupAt (0 : Fin 4) =
      {star.ownerAt (0 : Fin 4)} := by
    simpa [hspineEq, PrivateCupStar578.privateCupAt] using
      star.spine_inter_cupFor (star.ownerAt_mem (0 : Fin 4))
  have hformula := Finset.card_union_add_card_inter
    spine (star.privateCupAt (0 : Fin 4))
  rw [hspineCard, hprivateCard, hinter] at hformula
  simpa [PrivateCupStarSixCapState578.carrierAtFullSpine, star] using hformula

theorem PrivateCupStarSixCapState578.carrierAtFullSpine_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) :
    joint.carrierAtFullSpine hspine ⊆ support := by
  let star := joint.starAtFullSpine hspine
  have hspineSub : spine ⊆ support := by
    change star.spine ⊆ support
    exact (mem_capWitnesses.mp star.spine_mem).1
  change spine ∪ star.privateCupAt (0 : Fin 4) ⊆ support
  exact Finset.union_subset hspineSub
    (mem_capWitnesses.mp (star.privateCupAt_mem (0 : Fin 4))).1

/-- A three-vertex boundary covers all four-cups local to each canonical
full-spine carrier. -/
theorem PrivateCupStarSixCapState578.exists_localBoundaryAtFullSpine
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (hnoCup : ¬ContainsCupSet χ support 5)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ joint.carrierAtFullSpine hspine ∧
      boundary.card ≤ 3 ∧
      ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
        cup ⊆ joint.carrierAtFullSpine hspine →
          ¬Disjoint cup boundary := by
  rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
      (by rw [joint.carrierAtFullSpine_card hspine]) with
    hcupFive | ⟨boundary, hboundarySub, hboundaryCard, hhits⟩
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive
      (joint.carrierAtFullSpine_subset hspine))).elim
  · refine ⟨boundary, hboundarySub, hboundaryCard, ?_⟩
    intro cup hcup hcupSub
    have hcupData := mem_capWitnesses.mp hcup
    exact hhits.2 cup (mem_capWitnesses.mpr ⟨hcupSub, hcupData.2⟩)

/-- One local three-boundary for every full selected spine. -/
structure FullSpineLocalBoundarySystem578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  boundaryFor : ∀ spine,
    spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal → Finset (Fin n)
  boundaryFor_sub : ∀ spine hspine,
    boundaryFor spine hspine ⊆ joint.carrierAtFullSpine hspine
  boundaryFor_card : ∀ spine hspine,
    (boundaryFor spine hspine).card ≤ 3
  hits_local : ∀ spine hspine cup,
    cup ∈ capWitnesses χ.dual support 4 →
    cup ⊆ joint.carrierAtFullSpine hspine →
      ¬Disjoint cup (boundaryFor spine hspine)

theorem exists_fullSpineLocalBoundarySystem578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    Nonempty (FullSpineLocalBoundarySystem578 joint) := by
  classical
  have hexists : ∀ spine, ∀ hspine : spine ∈
      joint.saturation.state.packing.fullCupSpines joint.ledger.transversal,
      ∃ boundary : Finset (Fin n),
        boundary ⊆ joint.carrierAtFullSpine hspine ∧
        boundary.card ≤ 3 ∧
        ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
          cup ⊆ joint.carrierAtFullSpine hspine →
            ¬Disjoint cup boundary :=
    fun spine hspine ↦ joint.exists_localBoundaryAtFullSpine hnoCup hspine
  choose boundaryFor hsub hcard hhits using hexists
  exact ⟨{
    boundaryFor := boundaryFor
    boundaryFor_sub := hsub
    boundaryFor_card := hcard
    hits_local := hhits
  }⟩

/-- The union of the local boundaries over all full selected spines. -/
def FullSpineLocalBoundarySystem578.totalBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (system : FullSpineLocalBoundarySystem578 joint) : Finset (Fin n) :=
  let fullSpines := joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  fullSpines.attach.biUnion fun spine ↦
    system.boundaryFor spine spine.property

theorem FullSpineLocalBoundarySystem578.totalBoundary_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (system : FullSpineLocalBoundarySystem578 joint) :
    system.totalBoundary ⊆ support := by
  classical
  rw [FullSpineLocalBoundarySystem578.totalBoundary,
    Finset.biUnion_subset_iff_forall_subset]
  intro spine _
  exact (system.boundaryFor_sub spine spine.property).trans
    (joint.carrierAtFullSpine_subset spine.property)

theorem FullSpineLocalBoundarySystem578.totalBoundary_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (system : FullSpineLocalBoundarySystem578 joint) :
    system.totalBoundary.card ≤
      3 * (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).card := by
  classical
  let fullSpines := joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  have hle := Finset.card_biUnion_le_card_mul fullSpines.attach
    (fun spine ↦ system.boundaryFor spine spine.property) 3
    (by
      intro spine _
      exact system.boundaryFor_card spine spine.property)
  change (fullSpines.attach.biUnion fun spine ↦
    system.boundaryFor spine spine.property).card ≤ 3 * fullSpines.card
  calc
    _ ≤ fullSpines.attach.card * 3 := hle
    _ = 3 * fullSpines.card := by rw [Finset.card_attach]; omega

theorem FullSpineLocalBoundarySystem578.boundaryFor_subset_totalBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (system : FullSpineLocalBoundarySystem578 joint)
    {spine : Finset (Fin n)}
    (hspine : spine ∈ joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal) :
    system.boundaryFor spine hspine ⊆ system.totalBoundary := by
  classical
  let fullSpines := joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  let attachedSpine : fullSpines := ⟨spine, hspine⟩
  have hsubset := Finset.subset_biUnion_of_mem
    (fun indexed : fullSpines ↦
      system.boundaryFor indexed indexed.property)
    (Finset.mem_attach fullSpines attachedSpine)
  simpa [FullSpineLocalBoundarySystem578.totalBoundary,
    fullSpines, attachedSpine] using hsubset

/-- When there is exactly one full selected cup, the density obstruction to
an owner-plus-two-tail exchange produces a new seven-vertex residual cup
carrier meeting a different spine owner. -/
theorem exists_sevenVertexResidualCupCarrier578_for_owner_of_one_fullSpine_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1)
    (i : Fin 4) :
    ∃ carrier : SevenVertexResidualCupCarrier578 joint,
      carrier.owner = joint.star.ownerAt i := by
  classical
  let owner := joint.star.ownerAt i
  have hownerSpine : owner ∈ joint.star.spine :=
    joint.star.ownerAt_mem i
  have hownerTransversal : owner ∈ joint.ledger.transversal :=
    joint.star.spine_sub_transversal hownerSpine
  let tail := joint.ledger.tailFor owner hownerTransversal
  have htailCard : tail.card = 3 :=
    joint.ledger.tailFor_card owner hownerTransversal
  obtain ⟨gap, hgapTail⟩ : tail.Nonempty :=
    Finset.card_pos.mp (by rw [htailCard]; omega)
  let partialBoundary := insert owner (tail.erase gap)
  let candidate :=
    (joint.ledger.transversal \ joint.star.spine) ∪ partialBoundary
  have htransversalLe : joint.ledger.transversal.card ≤ 10 := by
    have hle :=
      joint.saturation.state.packing.transversal_card_le_nine_add_fullCupSpines
        joint.ledger.transversal_sub
    rw [hone] at hle
    omega
  have hunprotectedCard :
      (joint.ledger.transversal \ joint.star.spine).card ≤ 6 := by
    rw [Finset.card_sdiff_of_subset joint.star.spine_sub_transversal,
      joint.star.spine_card]
    omega
  have hownerNotTail : owner ∉ tail := by
    intro hownerTail
    exact (Finset.mem_erase.mp hownerTail).1 rfl
  have htailEraseCard : (tail.erase gap).card = 2 := by
    rw [Finset.card_erase_of_mem hgapTail, htailCard]
  have hpartialBoundaryCard : partialBoundary.card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · omega
    · intro hownerErase
      exact hownerNotTail (Finset.mem_erase.mp hownerErase).2
  have hcandidateCard : candidate.card ≤ 9 := by
    have hle := Finset.card_union_le
      (joint.ledger.transversal \ joint.star.spine) partialBoundary
    dsimp [candidate]
    omega
  have hcandidateSub : candidate ⊆ reservoir := by
    apply Finset.union_subset
    · exact Finset.sdiff_subset.trans joint.ledger.transversal_hits.1
    · intro x hxBoundary
      simp only [partialBoundary, Finset.mem_insert, Finset.mem_erase] at hxBoundary
      rcases hxBoundary with rfl | ⟨_, hxTail⟩
      · exact joint.ledger.transversal_hits.1 hownerTransversal
      · exact Finset.sdiff_subset
          (joint.ledger.tailFor_subset_sdiff owner hownerTransversal hxTail)
  obtain ⟨cup, hcup, hdisjointCandidate⟩ :=
    exists_fourCup_disjoint_from_of_card_le_nine_at_578
      hreservoir hcard hnoCap hnoStrong hcandidateSub hcandidateCard
  have hdisjointUnprotected :
      Disjoint cup (joint.ledger.transversal \ joint.star.spine) :=
    Disjoint.mono_right Finset.subset_union_left hdisjointCandidate
  have hdisjointBoundary : Disjoint cup partialBoundary :=
    Disjoint.mono_right Finset.subset_union_right hdisjointCandidate
  have hmeetsTransversal : ¬Disjoint cup joint.ledger.transversal :=
    joint.ledger.transversal_hits.2 cup hcup
  have hmeetsOtherOwner : ¬Disjoint cup (joint.star.spine.erase owner) := by
    obtain ⟨x, hxCup, hxTransversal⟩ :=
      Finset.not_disjoint_iff.mp hmeetsTransversal
    apply Finset.not_disjoint_iff.mpr
    refine ⟨x, hxCup, ?_⟩
    have hxSpine : x ∈ joint.star.spine := by
      by_contra hxNotSpine
      exact (Finset.disjoint_left.mp hdisjointUnprotected hxCup)
        (Finset.mem_sdiff.mpr ⟨hxTransversal, hxNotSpine⟩)
    have hxNeOwner : x ≠ owner := by
      intro hxEq
      subst x
      exact (Finset.disjoint_left.mp hdisjointBoundary hxCup) (by simp [partialBoundary])
    exact Finset.mem_erase.mpr ⟨hxNeOwner, hxSpine⟩
  have hmeetsSpine : ¬Disjoint cup joint.star.spine := by
    apply Finset.not_disjoint_iff.mpr
    obtain ⟨x, hxCup, hxOther⟩ := Finset.not_disjoint_iff.mp hmeetsOtherOwner
    exact ⟨x, hxCup, (Finset.mem_erase.mp hxOther).2⟩
  have hcupNeSpine : cup ≠ joint.star.spine := by
    intro hcupEq
    have hownerCup : owner ∈ cup := hcupEq.symm ▸ hownerSpine
    exact (Finset.disjoint_left.mp hdisjointBoundary hownerCup)
      (by simp [partialBoundary])
  have hinterPos : 1 ≤ (joint.star.spine ∩ cup).card :=
    Finset.card_pos.mpr (by
      obtain ⟨x, hxCup, hxSpine⟩ := Finset.not_disjoint_iff.mp hmeetsSpine
      exact ⟨x, Finset.mem_inter.mpr ⟨hxSpine, hxCup⟩⟩)
  have hcupCard := (mem_capWitnesses.mp hcup).2.1
  have hcarrierCard : (joint.star.spine ∪ cup).card ≤ 7 := by
    have hformula := Finset.card_union_add_card_inter joint.star.spine cup
    rw [joint.star.spine_card, hcupCard] at hformula
    omega
  refine ⟨{
    owner := owner
    owner_mem := hownerSpine
    omittedTailVertex := gap
    omittedTailVertex_mem := hgapTail
    cup := cup
    cup_mem := hcup
    avoids_unprotected := hdisjointUnprotected
    avoids_partialBoundary := hdisjointBoundary
    meets_other_owner := hmeetsOtherOwner
    cup_ne_spine := hcupNeSpine
    carrier_card := hcarrierCard
  }, ?_⟩
  rfl

/-- In particular, the tight one-spine branch always has at least one such
seven-vertex carrier. -/
theorem exists_sevenVertexResidualCupCarrier578_of_one_fullSpine_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    Nonempty (SevenVertexResidualCupCarrier578 joint) := by
  obtain ⟨carrier, _⟩ :=
    exists_sevenVertexResidualCupCarrier578_for_owner_of_one_fullSpine_at_32
      joint hreservoir hcard hnoCap hnoStrong hone (0 : Fin 4)
  exact ⟨carrier⟩

/-- The four owner-indexed partial exchanges in the tight branch. -/
structure FourOwnerResidualCupLedger578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  carrierAt : Fin 4 → SevenVertexResidualCupCarrier578 joint
  ownerAt_eq : ∀ i, (carrierAt i).owner = joint.star.ownerAt i

/-- Density supplies all four owner-indexed residual carriers
simultaneously. -/
theorem exists_fourOwnerResidualCupLedger578_of_one_fullSpine_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    Nonempty (FourOwnerResidualCupLedger578 joint) := by
  have hexists : ∀ i : Fin 4,
      ∃ carrier : SevenVertexResidualCupCarrier578 joint,
        carrier.owner = joint.star.ownerAt i :=
    fun i ↦
      exists_sevenVertexResidualCupCarrier578_for_owner_of_one_fullSpine_at_32
        joint hreservoir hcard hnoCap hnoStrong hone i
  choose carrierAt howner using hexists
  exact ⟨{ carrierAt := carrierAt, ownerAt_eq := howner }⟩

/-- The owner-indexed residual cup. -/
def FourOwnerResidualCupLedger578.cupAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint)
    (i : Fin 4) : Finset (Fin n) :=
  (ledger.carrierAt i).cup

theorem FourOwnerResidualCupLedger578.cupAt_mem
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) (i : Fin 4) :
    ledger.cupAt i ∈ capWitnesses χ.dual support 4 :=
  (ledger.carrierAt i).cup_mem

/-- The cup generated for an owner omits that owner. -/
theorem FourOwnerResidualCupLedger578.ownerAt_not_mem_cupAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) (i : Fin 4) :
    joint.star.ownerAt i ∉ ledger.cupAt i := by
  have hownerBoundary : (ledger.carrierAt i).owner ∈
      insert (ledger.carrierAt i).owner
        ((joint.ledger.tailFor (ledger.carrierAt i).owner
          (joint.star.spine_sub_transversal
            (ledger.carrierAt i).owner_mem)).erase
              (ledger.carrierAt i).omittedTailVertex) := by simp
  have hnot : (ledger.carrierAt i).owner ∉ (ledger.carrierAt i).cup := by
    intro hownerCup
    exact (Finset.disjoint_left.mp
      (ledger.carrierAt i).avoids_partialBoundary hownerCup) hownerBoundary
  simpa [FourOwnerResidualCupLedger578.cupAt, ledger.ownerAt_eq i] using hnot

/-- For every row there is another owner row whose cup is genuinely
different.  Thus the four partial exchanges cannot all collapse to one cup. -/
theorem FourOwnerResidualCupLedger578.exists_ne_cupAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) (i : Fin 4) :
    ∃ k : Fin 4, k ≠ i ∧ ledger.cupAt k ≠ ledger.cupAt i := by
  obtain ⟨x, hxCup, hxOtherOwner⟩ := Finset.not_disjoint_iff.mp
    (ledger.carrierAt i).meets_other_owner
  have hxSpine : x ∈ joint.star.spine :=
    (Finset.mem_erase.mp hxOtherOwner).2
  have hxRange : x ∈ Set.range
      (joint.star.spine.orderEmbOfFin joint.star.spine_card) := by
    rw [Finset.range_orderEmbOfFin]
    exact hxSpine
  obtain ⟨k, hk⟩ := hxRange
  have hkNe : k ≠ i := by
    intro hki
    subst k
    have hxNe := (Finset.mem_erase.mp hxOtherOwner).1
    exact hxNe (hk.symm.trans (ledger.ownerAt_eq i).symm)
  refine ⟨k, hkNe, ?_⟩
  intro heq
  have hxCupK : x ∈ ledger.cupAt k := by
    rw [heq]
    exact hxCup
  have hxOwnerK : x = joint.star.ownerAt k := by
    simpa [PrivateCupStar578.ownerAt] using hk.symm
  exact ledger.ownerAt_not_mem_cupAt k (hxOwnerK ▸ hxCupK)

/-- The second mixed matrix, now using the four cups forced by partial
owner-tail exchanges rather than the original private cups. -/
structure ResidualCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint)
    (tree : DecompositionTree χ support) where
  cell : ∀ i : Fin 4, ∀ j : Fin 6,
    CupCapFirstJointSplit578 tree
      (ledger.cupAt i) (joint.saturation.capAt j)

theorem exists_residualCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint)
    (tree : DecompositionTree χ support) :
    Nonempty (ResidualCupSixCapAddressMatrix578 ledger tree) := by
  classical
  exact ⟨{
    cell := fun i j ↦ Classical.choice
      (exists_cupCapFirstJointSplit578_general tree
        (ledger.cupAt_mem i) (joint.saturation.capAt_mem j))
  }⟩

/-- Each residual-cup row is again a prefix chain. -/
theorem ResidualCupSixCapAddressMatrix578.row_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree)
    (i : Fin 4) (j k : Fin 6) :
    (matrix.cell i j).path <+: (matrix.cell i k).path ∨
      (matrix.cell i k).path <+: (matrix.cell i j).path := by
  let cup := ledger.cupAt i
  have hcupData := mem_capWitnesses.mp (ledger.cupAt_mem i)
  have hcupCard : 2 ≤ cup.card := by rw [hcupData.2.1]; omega
  let cupPath := tree.lowestSeparatingPath hcupData.1 hcupCard
  have hprefix (column : Fin 6) :
      (matrix.cell i column).path <+: cupPath := by
    let cap := joint.saturation.capAt column
    have hcapData := mem_capWitnesses.mp
      (joint.saturation.capAt_mem column)
    have hunionSub : cup ∪ cap ⊆ support :=
      Finset.union_subset hcupData.1 hcapData.1
    have hunionCard : 2 ≤ (cup ∪ cap).card := by
      have hle := Finset.card_le_card
        (Finset.subset_union_left : cup ⊆ cup ∪ cap)
      rw [hcupData.2.1] at hle
      omega
    have hp := tree.lowestSeparatingPath_prefix_of_subset
      hcupData.1 hunionSub hcupCard hunionCard
      (Finset.subset_union_left : cup ⊆ cup ∪ cap)
    have hpathEq := (matrix.cell i column).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard
    rw [hpathEq]
    exact hp
  exact List.prefix_or_prefix_of_prefix (hprefix j) (hprefix k)

/-- Each of the six disjoint-cap columns is a prefix chain as well. -/
theorem ResidualCupSixCapAddressMatrix578.column_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree)
    (i k : Fin 4) (j : Fin 6) :
    (matrix.cell i j).path <+: (matrix.cell k j).path ∨
      (matrix.cell k j).path <+: (matrix.cell i j).path := by
  let cap := joint.saturation.capAt j
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hcapCard : 2 ≤ cap.card := by rw [hcapData.2.1]; omega
  let capPath := tree.lowestSeparatingPath hcapData.1 hcapCard
  have hprefix (row : Fin 4) :
      (matrix.cell row j).path <+: capPath := by
    let cup := ledger.cupAt row
    have hcupData := mem_capWitnesses.mp (ledger.cupAt_mem row)
    have hunionSub : cup ∪ cap ⊆ support :=
      Finset.union_subset hcupData.1 hcapData.1
    have hunionCard : 2 ≤ (cup ∪ cap).card := by
      have hle := Finset.card_le_card
        (Finset.subset_union_right : cap ⊆ cup ∪ cap)
      rw [hcapData.2.1] at hle
      omega
    have hp := tree.lowestSeparatingPath_prefix_of_subset
      hcapData.1 hunionSub hcapCard hunionCard
      (Finset.subset_union_right : cap ⊆ cup ∪ cap)
    have hpathEq := (matrix.cell row j).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard
    rw [hpathEq]
    exact hp
  exact List.prefix_or_prefix_of_prefix (hprefix i) (hprefix k)

/-- The residual-cup matrix inherits a global minimum address. -/
theorem ResidualCupSixCapAddressMatrix578.exists_globalMinimum
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree) :
    ∃ i₀ j₀, ∀ i j,
      (matrix.cell i₀ j₀).path <+: (matrix.cell i j).path :=
  exists_globalPrefixMinimum_fourBySix
    (fun i j ↦ (matrix.cell i j).path)
    matrix.row_paths_comparable matrix.column_paths_comparable

/-- A chosen global minimum for the residual-cup matrix. -/
structure ResidualCupSixCapCommonMinimum578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree) where
  row : Fin 4
  column : Fin 6
  minimal : ∀ i j, (matrix.cell row column).path <+: (matrix.cell i j).path

theorem ResidualCupSixCapAddressMatrix578.commonMinimum_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree) :
    Nonempty (ResidualCupSixCapCommonMinimum578 matrix) := by
  obtain ⟨row, column, hminimal⟩ := matrix.exists_globalMinimum
  exact ⟨{ row := row, column := column, minimal := hminimal }⟩

noncomputable def ResidualCupSixCapAddressMatrix578.commonMinimum
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    (matrix : ResidualCupSixCapAddressMatrix578 ledger tree) :
    ResidualCupSixCapCommonMinimum578 matrix :=
  Classical.choice matrix.commonMinimum_nonempty

/-- The second address matrix has the same exact one-sided/mixed rectangle
trichotomy as the original private-cup matrix. -/
theorem ResidualCupSixCapCommonMinimum578.oneSided_or_crossCorners
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    {matrix : ResidualCupSixCapAddressMatrix578 ledger tree}
    (minimum : ResidualCupSixCapCommonMinimum578 matrix) :
    (∀ i j, AddressAtOrExtends578
      (matrix.cell minimum.row minimum.column).path false
      (matrix.cell i j).path) ∨
    (∀ i j, AddressAtOrExtends578
      (matrix.cell minimum.row minimum.column).path true
      (matrix.cell i j).path) ∨
    ∃ i k j l,
      (matrix.cell i l).path =
          (matrix.cell minimum.row minimum.column).path ∧
        (matrix.cell k j).path =
          (matrix.cell minimum.row minimum.column).path :=
  fourBySix_oneSided_or_crossCorners
    (fun i j ↦ (matrix.cell i j).path)
    matrix.row_paths_comparable matrix.column_paths_comparable minimum.minimal

/-- Strict descent from the residual matrix minimum localizes the associated
exchange cup and cap block in the named child. -/
theorem ResidualCupSixCapCommonMinimum578.cell_union_subset_lower_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    {matrix : ResidualCupSixCapAddressMatrix578 ledger tree}
    (minimum : ResidualCupSixCapCommonMinimum578 matrix)
    {i : Fin 4} {j : Fin 6} {tail : List Bool}
    (hextends : (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: tail) :
    ledger.cupAt i ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.lower :=
  (matrix.cell i j).allocated.subset_lower_of_path_eq_append_false
    (matrix.cell minimum.row minimum.column).lookup hextends

theorem ResidualCupSixCapCommonMinimum578.cell_union_subset_upper_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    {matrix : ResidualCupSixCapAddressMatrix578 ledger tree}
    (minimum : ResidualCupSixCapCommonMinimum578 matrix)
    {i : Fin 4} {j : Fin 6} {tail : List Bool}
    (hextends : (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path ++ true :: tail) :
    ledger.cupAt i ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.upper :=
  (matrix.cell i j).allocated.subset_upper_of_path_eq_append_true
    (matrix.cell minimum.row minimum.column).lookup hextends

/-- Every seven-vertex residual carrier has a three-vertex boundary meeting
all four-cups which are local to that carrier.  Promoting this local coverage
to all residual cups is the remaining exchange obligation. -/
theorem SevenVertexResidualCupCarrier578.exists_localBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (carrier : SevenVertexResidualCupCarrier578 joint)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ joint.star.spine ∪ carrier.cup ∧
      boundary.card ≤ 3 ∧
      ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
        cup ⊆ joint.star.spine ∪ carrier.cup →
          ¬Disjoint cup boundary := by
  rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
      carrier.carrier_card with hcupFive | ⟨boundary, hboundarySub,
        hboundaryCard, hhits⟩
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive
      (Finset.union_subset
        (mem_capWitnesses.mp joint.star.spine_mem).1
        (mem_capWitnesses.mp carrier.cup_mem).1))).elim
  · refine ⟨boundary, hboundarySub, hboundaryCard, ?_⟩
    intro cup hcup hcupSub
    have hcupData := mem_capWitnesses.mp hcup
    exact hhits.2 cup (mem_capWitnesses.mpr
      ⟨hcupSub, hcupData.2⟩)

/-- For any proposed boundary with the exchange budget `3r`, density produces
a residual four-cup missed by that boundary.  This is the generic one-, two-,
and three-spine escape principle. -/
theorem exists_residualCup_disjoint_from_fullSpineBoundary578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir boundary : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hboundarySub : boundary ⊆ reservoir)
    (hboundaryCard : boundary.card ≤
      3 * (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).card) :
    ∃ cup,
      cup ∈ joint.ledger.residualCupFamily
        (joint.saturation.state.packing.fullCupProtected
          joint.ledger.transversal) ∧
      Disjoint cup boundary := by
  classical
  let fullSpines := joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  let protectedSet := joint.saturation.state.packing.fullCupProtected
    joint.ledger.transversal
  let candidate :=
    (joint.ledger.transversal \ protectedSet) ∪ boundary
  have hprotectedSub : protectedSet ⊆ joint.ledger.transversal :=
    joint.saturation.state.packing.fullCupProtected_subset
  have hprotectedCard : protectedSet.card = 4 * fullSpines.card := by
    exact joint.saturation.state.packing.fullCupProtected_card
  have htransversalLe : joint.ledger.transversal.card ≤
      9 + fullSpines.card :=
    joint.saturation.state.packing.transversal_card_le_nine_add_fullCupSpines
      joint.ledger.transversal_sub
  have hunprotectedCard :
      (joint.ledger.transversal \ protectedSet).card =
        joint.ledger.transversal.card - 4 * fullSpines.card := by
    rw [Finset.card_sdiff_of_subset hprotectedSub, hprotectedCard]
  have hcandidateCard : candidate.card ≤ 9 := by
    have hle := Finset.card_union_le
      (joint.ledger.transversal \ protectedSet) boundary
    have hprotectedLe := Finset.card_le_card hprotectedSub
    rw [hprotectedCard] at hprotectedLe
    dsimp [candidate, fullSpines] at hle hboundaryCard htransversalLe hunprotectedCard hprotectedLe ⊢
    omega
  have hcandidateSub : candidate ⊆ reservoir :=
    Finset.union_subset
      (Finset.sdiff_subset.trans joint.ledger.transversal_hits.1)
      hboundarySub
  obtain ⟨cup, hcup, hdisjointCandidate⟩ :=
    exists_fourCup_disjoint_from_of_card_le_nine_at_578
      hreservoir hcard hnoCap hnoStrong hcandidateSub hcandidateCard
  have hdisjointUnprotected :
      Disjoint cup (joint.ledger.transversal \ protectedSet) :=
    Disjoint.mono_right Finset.subset_union_left hdisjointCandidate
  have hdisjointBoundary : Disjoint cup boundary :=
    Disjoint.mono_right Finset.subset_union_right hdisjointCandidate
  exact ⟨cup, joint.ledger.mem_residualCupFamily.mpr
    ⟨hcup, hdisjointUnprotected⟩, hdisjointBoundary⟩

/-- The union of all local three-boundaries still misses a residual cup, and
that cup escapes every canonical full-spine seven-vertex carrier. -/
theorem FullSpineLocalBoundarySystem578.exists_residualCup_escaping_every_carrier
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (system : FullSpineLocalBoundarySystem578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ cup,
      cup ∈ joint.ledger.residualCupFamily
        (joint.saturation.state.packing.fullCupProtected
          joint.ledger.transversal) ∧
      Disjoint cup system.totalBoundary ∧
      ∀ spine, ∀ hspine : spine ∈
        joint.saturation.state.packing.fullCupSpines
          joint.ledger.transversal,
        ¬cup ⊆ joint.carrierAtFullSpine hspine := by
  obtain ⟨cup, hcupResidual, hdisjoint⟩ :=
    exists_residualCup_disjoint_from_fullSpineBoundary578 joint
      hreservoir hcard hnoCap hnoStrong system.totalBoundary_subset
      system.totalBoundary_card
  have hcup := (joint.ledger.mem_residualCupFamily.mp hcupResidual).1
  refine ⟨cup, hcupResidual, hdisjoint, ?_⟩
  intro spine hspine hcupSub
  have hdisjointLocal :
      Disjoint cup (system.boundaryFor spine hspine) :=
    Disjoint.mono_right
      (system.boundaryFor_subset_totalBoundary hspine) hdisjoint
  exact (system.hits_local spine hspine cup hcup hcupSub) hdisjointLocal

/-- Every residual cup still meets the protected union, because the original
owner transversal hits it and its unprotected part does not. -/
theorem PrivateCupLedger578.residualCup_meets_fullCupProtected
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {cup : Finset (Fin n)}
    (hcup : cup ∈ joint.ledger.residualCupFamily
      (joint.saturation.state.packing.fullCupProtected
        joint.ledger.transversal)) :
    ¬Disjoint cup (joint.saturation.state.packing.fullCupProtected
      joint.ledger.transversal) := by
  have hdata := joint.ledger.mem_residualCupFamily.mp hcup
  have hmeetsTransversal := joint.ledger.transversal_hits.2 cup hdata.1
  obtain ⟨x, hxCup, hxTransversal⟩ :=
    Finset.not_disjoint_iff.mp hmeetsTransversal
  apply Finset.not_disjoint_iff.mpr
  refine ⟨x, hxCup, ?_⟩
  by_contra hxProtected
  exact (Finset.disjoint_left.mp hdata.2 hxCup)
    (Finset.mem_sdiff.mpr ⟨hxTransversal, hxProtected⟩)

/-- The durable output of the all-spine local-boundary construction: a
residual cup meets one full spine but has a vertex outside that spine's
canonical private-cup carrier. -/
structure ExpandingFullSpineCarrier578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (system : FullSpineLocalBoundarySystem578 joint) where
  spine : Finset (Fin n)
  spine_mem : spine ∈ joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  cup : Finset (Fin n)
  cup_residual : cup ∈ joint.ledger.residualCupFamily
    (joint.saturation.state.packing.fullCupProtected
      joint.ledger.transversal)
  disjoint_totalBoundary : Disjoint cup system.totalBoundary
  meets_spine : ¬Disjoint cup spine
  outside_oldCarrier : (cup \ joint.carrierAtFullSpine spine_mem).Nonempty
  expandedCarrier_card : (spine ∪ cup).card ≤ 7

theorem FullSpineLocalBoundarySystem578.exists_expandingFullSpineCarrier
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (system : FullSpineLocalBoundarySystem578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (ExpandingFullSpineCarrier578 system) := by
  classical
  obtain ⟨cup, hcupResidual, hdisjoint, hescapes⟩ :=
    system.exists_residualCup_escaping_every_carrier
      hreservoir hcard hnoCap hnoStrong
  obtain ⟨x, hxCup, hxProtected⟩ := Finset.not_disjoint_iff.mp
    (PrivateCupLedger578.residualCup_meets_fullCupProtected
      (joint := joint) hcupResidual)
  have hxUnion : x ∈
      (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).biUnion id := by
    simpa [ThreeDisjointCupCapFourPacking578.fullCupProtected] using hxProtected
  obtain ⟨spine, hspine, hxSpine⟩ := Finset.mem_biUnion.mp hxUnion
  have hmeetsSpine : ¬Disjoint cup spine :=
    Finset.not_disjoint_iff.mpr ⟨x, hxCup, by simpa using hxSpine⟩
  obtain ⟨outside, houtsideCup, houtsideCarrier⟩ :=
    Finset.not_subset.mp (hescapes spine hspine)
  have houtside :
      (cup \ joint.carrierAtFullSpine hspine).Nonempty :=
    ⟨outside, Finset.mem_sdiff.mpr ⟨houtsideCup, houtsideCarrier⟩⟩
  have hspineCard := joint.saturation.state.packing.selectedCup_card
    (Finset.filter_subset _ _ hspine)
  have hcupCard :=
    (mem_capWitnesses.mp
      (joint.ledger.mem_residualCupFamily.mp hcupResidual).1).2.1
  have hinterPos : 1 ≤ (spine ∩ cup).card :=
    Finset.card_pos.mpr (by
      obtain ⟨y, hyCup, hySpine⟩ := Finset.not_disjoint_iff.mp hmeetsSpine
      exact ⟨y, Finset.mem_inter.mpr ⟨hySpine, hyCup⟩⟩)
  have hformula := Finset.card_union_add_card_inter spine cup
  have hcarrierCard : (spine ∪ cup).card ≤ 7 := by omega
  exact ⟨{
    spine := spine
    spine_mem := hspine
    cup := cup
    cup_residual := hcupResidual
    disjoint_totalBoundary := hdisjoint
    meets_spine := hmeetsSpine
    outside_oldCarrier := houtside
    expandedCarrier_card := hcarrierCard
  }⟩

/-- A three-vertex boundary which covers only a proper local carrier cannot
cover the full residual family in the tight one-spine branch.  Density forces
a residual four-cup escaping that carrier. -/
theorem exists_escapingResidualCup578_of_localBoundary
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir carrier boundary : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1)
    (hcarrierSub : carrier ⊆ reservoir)
    (hboundarySub : boundary ⊆ carrier)
    (hboundaryCard : boundary.card ≤ 3)
    (hlocalHits : ∀ cup, cup ∈ capWitnesses χ.dual reservoir 4 →
      cup ⊆ carrier → ¬Disjoint cup boundary) :
    ∃ cup,
      cup ∈ joint.ledger.residualCupFamily
        (joint.saturation.state.packing.fullCupProtected
          joint.ledger.transversal) ∧
      Disjoint cup boundary ∧ ¬cup ⊆ carrier := by
  classical
  let protectedSet := joint.saturation.state.packing.fullCupProtected
    joint.ledger.transversal
  let candidate :=
    (joint.ledger.transversal \ protectedSet) ∪ boundary
  have hprotectedSub : protectedSet ⊆ joint.ledger.transversal :=
    joint.saturation.state.packing.fullCupProtected_subset
  have hprotectedCard : protectedSet.card = 4 := by
    have hprotected :=
      joint.saturation.state.packing.fullCupProtected_card
        (transversal := joint.ledger.transversal)
    dsimp [protectedSet]
    rw [hprotected, hone]
  have htransversalCard : joint.ledger.transversal.card = 10 :=
    joint.transversal_card_eq_ten_of_fullCupSpines_card_eq_one hone
  have hunprotectedCard :
      (joint.ledger.transversal \ protectedSet).card = 6 := by
    rw [Finset.card_sdiff_of_subset hprotectedSub,
      htransversalCard, hprotectedCard]
  have hcandidateCard : candidate.card ≤ 9 := by
    have hle := Finset.card_union_le
      (joint.ledger.transversal \ protectedSet) boundary
    dsimp [candidate]
    omega
  have hcandidateSub : candidate ⊆ reservoir :=
    Finset.union_subset
      (Finset.sdiff_subset.trans joint.ledger.transversal_hits.1)
      (hboundarySub.trans hcarrierSub)
  obtain ⟨cup, hcup, hdisjointCandidate⟩ :=
    exists_fourCup_disjoint_from_of_card_le_nine_at_578
      hreservoir hcard hnoCap hnoStrong hcandidateSub hcandidateCard
  have hdisjointUnprotected :
      Disjoint cup (joint.ledger.transversal \ protectedSet) :=
    Disjoint.mono_right Finset.subset_union_left hdisjointCandidate
  have hdisjointBoundary : Disjoint cup boundary :=
    Disjoint.mono_right Finset.subset_union_right hdisjointCandidate
  have hresidual : cup ∈ joint.ledger.residualCupFamily protectedSet :=
    joint.ledger.mem_residualCupFamily.mpr
      ⟨hcup, hdisjointUnprotected⟩
  refine ⟨cup, hresidual, hdisjointBoundary, ?_⟩
  intro hcupSub
  exact (hlocalHits cup hcup hcupSub) hdisjointBoundary

/-- Applying the escape lemma to the canonical local boundary shows that one
seven-vertex carrier necessarily generates a residual cup outside itself. -/
theorem SevenVertexResidualCupCarrier578.exists_escapingResidualCup
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (carrier : SevenVertexResidualCupCarrier578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    ∃ boundary cup,
      boundary ⊆ joint.star.spine ∪ carrier.cup ∧
      boundary.card ≤ 3 ∧
      cup ∈ joint.ledger.residualCupFamily
        (joint.saturation.state.packing.fullCupProtected
          joint.ledger.transversal) ∧
      Disjoint cup boundary ∧
      ¬cup ⊆ joint.star.spine ∪ carrier.cup := by
  obtain ⟨boundary, hboundarySub, hboundaryCard, hlocalHits⟩ :=
    carrier.exists_localBoundary hnoCup
  obtain ⟨cup, hcupResidual, hdisjoint, hescapes⟩ :=
    exists_escapingResidualCup578_of_localBoundary joint
      hreservoir hcard hnoCap hnoStrong hone
      (Finset.union_subset
        (mem_capWitnesses.mp joint.star.spine_mem).1
        (mem_capWitnesses.mp carrier.cup_mem).1)
      hboundarySub hboundaryCard hlocalHits
  exact ⟨boundary, cup, hboundarySub, hboundaryCard,
    hcupResidual, hdisjoint, hescapes⟩

/-- Reconnect the exchange machinery to the exact singleton-root gate.  Apart
from the fourth-disjoint-cup branch, either at least two selected cups are
fully protected, or the tight one-spine branch supplies the four-owner
residual-cup ledger and its second `4 × 6` address matrix. -/
theorem exists_fourthDisjointCup_or_twoFullSpines_or_residualAddressMatrix_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
    ∃ joint : PrivateCupStarSixCapState578 χ reservoir,
      2 ≤ (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).card ∨
      ((joint.saturation.state.packing.fullCupSpines
          joint.ledger.transversal).card = 1 ∧
        ∃ ledger : FourOwnerResidualCupLedger578 joint,
          ∃ tree : DecompositionTree χ reservoir,
            Nonempty (ResidualCupSixCapAddressMatrix578 ledger tree)) := by
  rcases exists_fourthDisjointCup_or_privateCupStarSixCapState_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | hjoint
  · exact Or.inl hfourth
  · right
    obtain ⟨joint⟩ := hjoint
    refine ⟨joint, ?_⟩
    by_cases hone : (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).card = 1
    · right
      refine ⟨hone, ?_⟩
      obtain ⟨ledger⟩ :=
        exists_fourOwnerResidualCupLedger578_of_one_fullSpine_at_32
          joint hreservoir hcard hnoCap hnoStrong hone
      obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hreservoir
      exact ⟨ledger, tree,
        exists_residualCupSixCapAddressMatrix578 ledger tree⟩
    · left
      have hnonempty := joint.fullCupSpines_nonempty
      have hpositive : 0 < (joint.saturation.state.packing.fullCupSpines
          joint.ledger.transversal).card := Finset.card_pos.mpr hnonempty
      omega

/-- A route-independent reconnection of the all-spine exchange wave: unless a
fourth selected-disjoint cup already exists, the exact gate supplies local
three-boundaries for every full spine and an expanded seven-vertex carrier
which escapes the corresponding old private-cup carrier. -/
theorem exists_fourthDisjointCup_or_expandingFullSpineCarrier_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
    ∃ joint : PrivateCupStarSixCapState578 χ reservoir,
      ∃ system : FullSpineLocalBoundarySystem578 joint,
        Nonempty (ExpandingFullSpineCarrier578 system) := by
  rcases exists_fourthDisjointCup_or_privateCupStarSixCapState_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | hjoint
  · exact Or.inl hfourth
  · right
    obtain ⟨joint⟩ := hjoint
    have hnoCupReservoir : ¬ContainsCupSet χ reservoir 5 := by
      intro hcup
      exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
        Finset.subset_union_right)
    obtain ⟨system⟩ :=
      exists_fullSpineLocalBoundarySystem578 joint hnoCupReservoir
    exact ⟨joint, system,
      system.exists_expandingFullSpineCarrier
        hreservoir hcard hnoCap hnoStrong⟩

/-- Under the exact density hypotheses, a full-spine residual boundary is
already contradictory. -/
theorem FullSpineResidualBoundary578.false_of_colorDualLower_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (residual : FullSpineResidualBoundary578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    False :=
  residual.toPrivateCupBoundaryExchange.false_of_colorDualLower_at_32
    hreservoir hcard hnoCap hnoStrong

end ErdosSzekeres

end
