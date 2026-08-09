module

public import ErdosSzekeres.StructuralChargingNextState578BoundaryExchange

@[expose] public section

/-!
# Carrier and full-residual matrix refinements at state `(5,7,8)`

This file repairs the witness-dropping mixed-address classification and
connects the tight one-spine residual cups to their actual owner incidences.
It also records the intersection synchronization needed to pass from four
sampled residual cups to the complete residual family.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-! ## Owner incidence and the exact three-owner compression -/

/-- A chosen other spine owner contained in every owner-indexed residual cup. -/
structure FourOwnerResidualCupLedger578.OwnerIncidence
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) where
  target : Fin 4 → Fin 4
  target_ne : ∀ i, target i ≠ i
  target_mem : ∀ i, joint.star.ownerAt (target i) ∈ ledger.cupAt i

/-- Each residual row contains some owner different from its source owner. -/
theorem FourOwnerResidualCupLedger578.exists_otherOwner_mem_cupAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) (i : Fin 4) :
    ∃ k : Fin 4, k ≠ i ∧ joint.star.ownerAt k ∈ ledger.cupAt i := by
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
  simpa [PrivateCupStar578.ownerAt] using hk ▸ hxCup

/-- Every four-owner ledger has a nonloop owner-incidence choice. -/
theorem FourOwnerResidualCupLedger578.ownerIncidence_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) :
    Nonempty ledger.OwnerIncidence := by
  choose target htargetNe htargetMem using ledger.exists_otherOwner_mem_cupAt
  exact ⟨{
    target := target
    target_ne := htargetNe
    target_mem := htargetMem
  }⟩

/-- A canonical owner-incidence choice for downstream constructions. -/
noncomputable def FourOwnerResidualCupLedger578.ownerIncidence
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : FourOwnerResidualCupLedger578 joint) : ledger.OwnerIncidence :=
  Classical.choice ledger.ownerIncidence_nonempty

/-- An incidence edge always connects two genuinely different residual cups. -/
theorem FourOwnerResidualCupLedger578.OwnerIncidence.target_cup_ne
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) (i : Fin 4) :
    ledger.cupAt (incidence.target i) ≠ ledger.cupAt i := by
  intro heq
  exact ledger.ownerAt_not_mem_cupAt (incidence.target i)
    (heq ▸ incidence.target_mem i)

/-- The spine vertices selected by the owner-incidence image. -/
def FourOwnerResidualCupLedger578.OwnerIncidence.boundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) : Finset (Fin n) :=
  (Finset.univ.image incidence.target).image joint.star.ownerAt

/-- Unless the owner map is a fixed-point-free permutation, its image gives
a three-vertex spine boundary hitting all four sampled residual cups. -/
theorem FourOwnerResidualCupLedger578.OwnerIncidence.injective_or_threeSpineBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) :
    Function.Injective incidence.target ∨
      (incidence.boundary ⊆ joint.star.spine ∧
        incidence.boundary.card ≤ 3 ∧
        ∀ i, ¬Disjoint (ledger.cupAt i) incidence.boundary) := by
  classical
  by_cases hinj : Function.Injective incidence.target
  · exact Or.inl hinj
  · right
    have hindexCard : (Finset.univ.image incidence.target).card ≤ 3 := by
      have hle : (Finset.univ.image incidence.target).card ≤
          (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      have hleFour : (Finset.univ.image incidence.target).card ≤ 4 := by
        simpa using hle
      have hne : (Finset.univ.image incidence.target).card ≠ 4 := by
        intro heq
        have hcardEq : (Finset.univ.image incidence.target).card =
            (Finset.univ : Finset (Fin 4)).card := by simpa using heq
        have hinjOn := Finset.card_image_iff.mp hcardEq
        apply hinj
        intro i j hij
        exact hinjOn (by simp) (by simp) hij
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact joint.star.ownerAt_mem k
    · have hle : incidence.boundary.card ≤
          (Finset.univ.image incidence.target).card := Finset.card_image_le
      exact hle.trans hindexCard
    · intro i
      apply Finset.not_disjoint_iff.mpr
      refine ⟨joint.star.ownerAt (incidence.target i), incidence.target_mem i, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨incidence.target i, ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

/-- Pair a residual cup with the private cup owned by one of its contained
spine vertices.  Unlike the source-owner pairing, this carrier has at most
seven vertices. -/
def FourOwnerResidualCupLedger578.OwnerIncidence.targetCarrier
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) (i : Fin 4) : Finset (Fin n) :=
  ledger.cupAt i ∪ joint.star.privateCupAt (incidence.target i)

theorem FourOwnerResidualCupLedger578.OwnerIncidence.targetCarrier_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) (i : Fin 4) :
    incidence.targetCarrier i ⊆ support :=
  Finset.union_subset
    (mem_capWitnesses.mp (ledger.cupAt_mem i)).1
    (mem_capWitnesses.mp (joint.star.privateCupAt_mem (incidence.target i))).1

theorem FourOwnerResidualCupLedger578.OwnerIncidence.targetCarrier_card_le_seven
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence) (i : Fin 4) :
    (incidence.targetCarrier i).card ≤ 7 := by
  have hresidualCard := (mem_capWitnesses.mp (ledger.cupAt_mem i)).2.1
  have hprivateCard :=
    (mem_capWitnesses.mp (joint.star.privateCupAt_mem (incidence.target i))).2.1
  have hinterPos : 1 ≤
      (ledger.cupAt i ∩ joint.star.privateCupAt (incidence.target i)).card := by
    apply Finset.card_pos.mpr
    refine ⟨joint.star.ownerAt (incidence.target i), Finset.mem_inter.mpr
      ⟨incidence.target_mem i, ?_⟩⟩
    exact joint.ledger.owner_mem_cupFor _ _
  have hformula := Finset.card_union_add_card_inter
    (ledger.cupAt i) (joint.star.privateCupAt (incidence.target i))
  rw [hresidualCard, hprivateCard] at hformula
  simpa [FourOwnerResidualCupLedger578.OwnerIncidence.targetCarrier] using
    (show (ledger.cupAt i ∪
      joint.star.privateCupAt (incidence.target i)).card ≤ 7 by omega)

/-- Every target-owner carrier has a local three-boundary unless it already
contains a five-cup. -/
theorem FourOwnerResidualCupLedger578.OwnerIncidence.exists_localBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    (incidence : ledger.OwnerIncidence)
    (hnoCup : ¬ContainsCupSet χ support 5) (i : Fin 4) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ incidence.targetCarrier i ∧
      boundary.card ≤ 3 ∧
      ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
        cup ⊆ incidence.targetCarrier i → ¬Disjoint cup boundary := by
  rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
      (incidence.targetCarrier_card_le_seven i) with
    hcupFive | ⟨boundary, hboundarySub, hboundaryCard, hhits⟩
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive
      (incidence.targetCarrier_subset i))).elim
  · refine ⟨boundary, hboundarySub, hboundaryCard, ?_⟩
    intro cup hcup hcupSub
    have hcupData := mem_capWitnesses.mp hcup
    exact hhits.2 cup (mem_capWitnesses.mpr ⟨hcupSub, hcupData.2⟩)

/-! ## The exact eight-vertex hypergraph obstruction -/

/-- Every five-subset of a carrier contains a four-cup.  This incidence
condition is exactly what remains on eight vertices when a three-vertex
four-cup transversal does not exist. -/
def HasFourCupInEveryFiveSubset578
    {n : ℕ} (χ : TripleColoring n) (carrier : Finset (Fin n)) : Prop :=
  ∀ five : Finset (Fin n), five ⊆ carrier → five.card = 5 →
    ∃ cup, cup ∈ capWitnesses χ.dual carrier 4 ∧ cup ⊆ five

/-- Failure of every three-vertex boundary on an eight-vertex carrier forces
the dense five-subset condition.  No decomposability assumption is used. -/
theorem hasFourCupInEveryFiveSubset_of_no_threeTransversal
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hcard : carrier.card = 8)
    (hnoBoundary : ¬∃ boundary : Finset (Fin n),
      boundary ⊆ carrier ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ carrier boundary 4) :
    HasFourCupInEveryFiveSubset578 χ carrier := by
  intro five hfiveSub hfiveCard
  let boundary := carrier \ five
  have hboundarySub : boundary ⊆ carrier := Finset.sdiff_subset
  have hboundaryCard : boundary.card = 3 := by
    rw [Finset.card_sdiff_of_subset hfiveSub, hcard, hfiveCard]
  have hnotHits : ¬IsCupWitnessTransversal578 χ carrier boundary 4 := by
    intro hhits
    exact hnoBoundary ⟨boundary, hboundarySub, by omega, hhits⟩
  have hnotAll : ¬∀ cup, cup ∈ capWitnesses χ.dual carrier 4 →
      ¬Disjoint cup boundary := by
    intro hall
    exact hnotHits ⟨hboundarySub, hall⟩
  push Not at hnotAll
  obtain ⟨cup, hcup, hdisjoint⟩ := hnotAll
  refine ⟨cup, hcup, ?_⟩
  intro x hxCup
  by_contra hxFive
  have hxBoundary : x ∈ boundary :=
    Finset.mem_sdiff.mpr ⟨(mem_capWitnesses.mp hcup).1 hxCup, hxFive⟩
  exact (Finset.disjoint_left.mp hdisjoint) hxCup hxBoundary

/-- On exactly eight vertices, a three-vertex four-cup transversal exists
precisely when some five-subset contains no four-cup. -/
theorem exists_threeTransversal_iff_exists_fiveSubset_without_fourCup
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hcard : carrier.card = 8) :
    (∃ boundary : Finset (Fin n),
      boundary ⊆ carrier ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ carrier boundary 4) ↔
    (∃ five : Finset (Fin n),
      five ⊆ carrier ∧ five.card = 5 ∧
        ¬∃ cup, cup ∈ capWitnesses χ.dual carrier 4 ∧ cup ⊆ five) := by
  classical
  constructor
  · rintro ⟨boundary, hboundarySub, hboundaryCard, hboundary⟩
    have hrestCard : 5 ≤ (carrier \ boundary).card := by
      rw [Finset.card_sdiff_of_subset hboundarySub, hcard]
      omega
    obtain ⟨five, hfiveSub, hfiveCard⟩ :=
      Finset.exists_subset_card_eq hrestCard
    refine ⟨five, hfiveSub.trans Finset.sdiff_subset, hfiveCard, ?_⟩
    rintro ⟨cup, hcup, hcupSub⟩
    apply hboundary.2 cup hcup
    apply Finset.disjoint_left.mpr
    intro x hxCup hxBoundary
    exact (Finset.mem_sdiff.mp (hfiveSub (hcupSub hxCup))).2 hxBoundary
  · rintro ⟨five, hfiveSub, hfiveCard, hnoCup⟩
    let boundary := carrier \ five
    have hboundarySub : boundary ⊆ carrier := Finset.sdiff_subset
    have hboundaryCard : boundary.card = 3 := by
      rw [Finset.card_sdiff_of_subset hfiveSub, hcard, hfiveCard]
    refine ⟨boundary, hboundarySub, by omega, hboundarySub, ?_⟩
    intro cup hcup hdisjoint
    apply hnoCup
    refine ⟨cup, hcup, ?_⟩
    intro x hxCup
    by_contra hxFive
    have hxBoundary : x ∈ boundary :=
      Finset.mem_sdiff.mpr ⟨(mem_capWitnesses.mp hcup).1 hxCup, hxFive⟩
    exact (Finset.disjoint_left.mp hdisjoint) hxCup hxBoundary

/-- The first genuine decomposable eight-vertex case: if the lower child of
the root is a singleton, every four-cup lies in the at-most-seven-vertex upper
child, so the seven-vertex transversal theorem closes the carrier. -/
theorem rootLowerSingleton_fourCupFamily_has_threeTransversal_or_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcard : (lower ∪ upper).card ≤ 8)
    (hlowerCard : lower.card = 1) :
    ContainsCupSet χ (lower ∪ upper) 5 ∨
      ∃ transversal : Finset (Fin n),
        transversal ⊆ lower ∪ upper ∧ transversal.card ≤ 3 ∧
          IsCupWitnessTransversal578 χ (lower ∪ upper) transversal 4 := by
  classical
  have hupperCard : upper.card ≤ 7 := by
    rw [Finset.card_union_of_disjoint hdeep.disjoint, hlowerCard] at hcard
    omega
  have cup_subset_upper (cup : Finset (Fin n))
      (hcup : cup ∈ capWitnesses χ.dual (lower ∪ upper) 4) :
      cup ⊆ upper := by
    have hcupData := mem_capWitnesses.mp hcup
    have hcupSet : IsCupSet χ cup := isCapSet_dual_iff.mp hcupData.2.2
    by_contra hnotSub
    have hcupLower : (cup ∩ lower).Nonempty := by
      rw [Finset.not_subset] at hnotSub
      obtain ⟨x, hxCup, hxNotUpper⟩ := hnotSub
      have hxLower : x ∈ lower := by
        rcases Finset.mem_union.mp (hcupData.1 hxCup) with hxLower | hxUpper
        · exact hxLower
        · exact (hxNotUpper hxUpper).elim
      exact ⟨x, Finset.mem_inter.mpr ⟨hxCup, hxLower⟩⟩
    have hupperInter := hdeep.cup_inter_upper_card_le_two
      hcupData.1 hcupSet hcupLower
    have hlowerInter : (cup ∩ lower).card ≤ 1 := by
      have hle := Finset.card_le_card
        (Finset.inter_subset_right : cup ∩ lower ⊆ lower)
      simpa [hlowerCard] using hle
    have hpartition : cup = (cup ∩ lower) ∪ (cup ∩ upper) := by
      apply Finset.Subset.antisymm
      · intro x hxCup
        rcases Finset.mem_union.mp (hcupData.1 hxCup) with hxLower | hxUpper
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxCup, hxLower⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxCup, hxUpper⟩)
      · exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hinterDisjoint : Disjoint (cup ∩ lower) (cup ∩ upper) :=
      hdeep.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [hpartition, Finset.card_union_of_disjoint hinterDisjoint] at hcupData
    omega
  rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
      (χ := χ) (carrier := upper) hupperCard with
    hcupFive | ⟨transversal, htransversalSub,
        htransversalCard, htransversal⟩
  · exact Or.inl (FinsetPolygon.ContainsCupSet.mono hcupFive
      Finset.subset_union_right)
  · right
    refine ⟨transversal, htransversalSub.trans Finset.subset_union_right,
      htransversalCard, htransversalSub.trans Finset.subset_union_right, ?_⟩
    intro cup hcup
    have hcupData := mem_capWitnesses.mp hcup
    exact htransversal.2 cup (mem_capWitnesses.mpr
      ⟨cup_subset_upper cup hcup, hcupData.2⟩)

/-! ## Witness-carrying address classification -/

/-- The indexed cap family really covers the entire six-cap support. -/
theorem SixCapSaturation578.capSupport_subset_of_all_capAt_subset
    {n : ℕ} {χ : TripleColoring n} {support target : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hcap : ∀ j : Fin 6, saturation.capAt j ⊆ target) :
    saturation.capSupport ⊆ target := by
  rw [SixCapSaturation578.capSupport,
    SevenWitnessRegenerationPacking578.fourCapSupport,
    ThreeDisjointCupCapFourPacking578.capSupport]
  exact Finset.union_subset
    (Finset.union_subset
      (Finset.union_subset
        (hcap 0)
        (Finset.union_subset
          (Finset.union_subset (hcap 1) (hcap 2))
          (hcap 3)))
      (hcap 4))
    (hcap 5)

/-- The non-vacuous address trichotomy retains the two strict witnesses in
the mixed branch, together with the cross-corner equalities they force. -/
theorem fourBySix_oneSided_or_oppositeExtensions
    (path : Fin 4 → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j)
    {i₀ : Fin 4} {j₀ : Fin 6}
    (hminimum : ∀ i j, path i₀ j₀ <+: path i j) :
    (∀ i j, AddressAtOrExtends578 (path i₀ j₀) false (path i j)) ∨
    (∀ i j, AddressAtOrExtends578 (path i₀ j₀) true (path i j)) ∨
    ∃ i k j l leftTail rightTail,
      path i j = path i₀ j₀ ++ false :: leftTail ∧
      path k l = path i₀ j₀ ++ true :: rightTail ∧
      path i l = path i₀ j₀ ∧ path k j = path i₀ j₀ := by
  let base := path i₀ j₀
  by_cases hleft : ∃ i j tail, path i j = base ++ false :: tail
  · by_cases hright : ∃ k l tail, path k l = base ++ true :: tail
    · rcases hleft with ⟨i, j, leftTail, hleft⟩
      rcases hright with ⟨k, l, rightTail, hright⟩
      obtain ⟨hcross₁, hcross₂⟩ :=
        fourBySix_crossCorners_eq_of_oppositeExtensions
          path hrow hcolumn hminimum hleft hright
      exact Or.inr (Or.inr ⟨i, k, j, l, leftTail, rightTail,
        hleft, hright, hcross₁, hcross₂⟩)
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

/-- The residual matrix inherits the repaired witness-carrying trichotomy. -/
theorem ResidualCupSixCapCommonMinimum578.oneSided_or_oppositeExtensions
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
    ∃ i k j l leftTail rightTail,
      (matrix.cell i j).path =
        (matrix.cell minimum.row minimum.column).path ++ false :: leftTail ∧
      (matrix.cell k l).path =
        (matrix.cell minimum.row minimum.column).path ++ true :: rightTail ∧
      (matrix.cell i l).path =
        (matrix.cell minimum.row minimum.column).path ∧
      (matrix.cell k j).path =
        (matrix.cell minimum.row minimum.column).path :=
  fourBySix_oneSided_or_oppositeExtensions
    (fun i j ↦ (matrix.cell i j).path)
    matrix.row_paths_comparable matrix.column_paths_comparable minimum.minimal

/-- The sharp collective output: all six caps localize in one child, an
entire cap column remains at the minimum, or explicit opposite strict cells
and their two cross-corners remain available. -/
theorem ResidualCupSixCapCommonMinimum578.localizedCaps_or_minimumColumn_or_mixedRectangle
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {ledger : FourOwnerResidualCupLedger578 joint}
    {tree : DecompositionTree χ support}
    {matrix : ResidualCupSixCapAddressMatrix578 ledger tree}
    (minimum : ResidualCupSixCapCommonMinimum578 matrix) :
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card) ∨
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card) ∨
    (∃ j, ∀ i, (matrix.cell i j).path =
      (matrix.cell minimum.row minimum.column).path) ∨
    ∃ i k j l leftTail rightTail,
      (matrix.cell i j).path =
        (matrix.cell minimum.row minimum.column).path ++ false :: leftTail ∧
      (matrix.cell k l).path =
        (matrix.cell minimum.row minimum.column).path ++ true :: rightTail ∧
      (matrix.cell i l).path =
        (matrix.cell minimum.row minimum.column).path ∧
      (matrix.cell k j).path =
        (matrix.cell minimum.row minimum.column).path := by
  classical
  rcases minimum.oneSided_or_oppositeExtensions with
    hleft | hright | hmixed
  · by_cases hall : ∀ j, ∃ i tail,
        (matrix.cell i j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: tail
    · left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.lower := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨i, tail, hstrict⟩ := hall j
        exact Finset.subset_union_right.trans
          (minimum.cell_union_subset_lower_of_extends hstrict)
      exact ⟨hsub, by
        have hcard := Finset.card_le_card hsub
        rw [joint.saturation.capSupport_card] at hcard
        exact hcard⟩
    · push Not at hall
      right
      right
      left
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun i ↦ ?_⟩
      rcases hleft i j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj i tail hstrict).elim
  · by_cases hall : ∀ j, ∃ i tail,
        (matrix.cell i j).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: tail
    · right
      left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.upper := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨i, tail, hstrict⟩ := hall j
        exact Finset.subset_union_right.trans
          (minimum.cell_union_subset_upper_of_extends hstrict)
      exact ⟨hsub, by
        have hcard := Finset.card_le_card hsub
        rw [joint.saturation.capSupport_card] at hcard
        exact hcard⟩
    · push Not at hall
      right
      right
      left
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun i ↦ ?_⟩
      rcases hright i j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj i tail hstrict).elim
  · exact Or.inr (Or.inr (Or.inr hmixed))

/-! ## Intersection synchronization -/

/-- Intersecting cup rows cannot leave a common ancestor in opposite
directions: localization would put their shared vertex in disjoint children. -/
theorem cupRows_not_opposite_of_inter
    {n : ℕ} {χ : TripleColoring n}
    {support cup₁ cup₂ cap₁ cap₂ : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    {base leftTail rightTail : List Bool}
    {node : DecompositionSplit χ}
    (cell₁ : CupCapFirstJointSplit578 tree cup₁ cap₁)
    (cell₂ : CupCapFirstJointSplit578 tree cup₂ cap₂)
    (hinter : ¬Disjoint cup₁ cup₂)
    (hlookup : tree.splitAtPath base = some node)
    (hleft : cell₁.path = base ++ false :: leftTail)
    (hright : cell₂.path = base ++ true :: rightTail) :
    False := by
  have hcup₁Lower : cup₁ ⊆ node.lower :=
    Finset.subset_union_left.trans
      (cell₁.allocated.subset_lower_of_path_eq_append_false hlookup hleft)
  have hcup₂Upper : cup₂ ⊆ node.upper :=
    Finset.subset_union_left.trans
      (cell₂.allocated.subset_upper_of_path_eq_append_true hlookup hright)
  obtain ⟨x, hx₁, hx₂⟩ := Finset.not_disjoint_iff.mp hinter
  exact (Finset.disjoint_left.mp node.deep.disjoint)
    (hcup₁Lower hx₁) (hcup₂Upper hx₂)

/-- The symmetric ordering of the intersection synchronization lemma. -/
theorem cupRows_not_opposite_of_inter'
    {n : ℕ} {χ : TripleColoring n}
    {support cup₁ cup₂ cap₁ cap₂ : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    {base leftTail rightTail : List Bool}
    {node : DecompositionSplit χ}
    (cell₁ : CupCapFirstJointSplit578 tree cup₁ cap₁)
    (cell₂ : CupCapFirstJointSplit578 tree cup₂ cap₂)
    (hinter : ¬Disjoint cup₁ cup₂)
    (hlookup : tree.splitAtPath base = some node)
    (hright : cell₁.path = base ++ true :: rightTail)
    (hleft : cell₂.path = base ++ false :: leftTail) :
    False := by
  have hinter' : ¬Disjoint cup₂ cup₁ := by
    obtain ⟨x, hx₁, hx₂⟩ := Finset.not_disjoint_iff.mp hinter
    exact Finset.not_disjoint_iff.mpr ⟨x, hx₂, hx₁⟩
  exact cupRows_not_opposite_of_inter cell₂ cell₁ hinter' hlookup hleft hright

/-! ## The complete residual-family matrix and its spine anchor -/

/-- The full spine itself belongs to the residual family obtained by removing
the unprotected part of the owner transversal. -/
theorem PrivateCupStarSixCapState578.spine_mem_residualCupFamily
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) :
    joint.star.spine ∈ joint.ledger.residualCupFamily joint.star.spine := by
  apply joint.ledger.mem_residualCupFamily.mpr
  refine ⟨joint.star.spine_mem, ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hxSpine hxUnprotected
  exact (Finset.mem_sdiff.mp hxUnprotected).2 hxSpine

/-- In the tight branch, every cup in the full residual family meets the
unique protected spine. -/
theorem PrivateCupStarSixCapState578.residualCup_meets_spine_of_card_eq_one
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1)
    {cup : Finset (Fin n)}
    (hcup : cup ∈ joint.ledger.residualCupFamily joint.star.spine) :
    ¬Disjoint cup joint.star.spine := by
  have heq := joint.fullCupProtected_eq_spine_of_card_eq_one hone
  have hcup' : cup ∈ joint.ledger.residualCupFamily
      (joint.saturation.state.packing.fullCupProtected
        joint.ledger.transversal) := by
    rwa [heq]
  have hmeet := PrivateCupLedger578.residualCup_meets_fullCupProtected
    (joint := joint) hcup'
  rwa [heq] at hmeet

/-- The finite type of all four-cups which avoid the unprotected part of the
owner transversal in the one-spine normalization. -/
def PrivateCupStarSixCapState578.ResidualCupIndex
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) : Type :=
  { cup : Finset (Fin n) //
    cup ∈ joint.ledger.residualCupFamily joint.star.spine }

/-- The spine as the distinguished residual-family row. -/
def PrivateCupStarSixCapState578.spineResidualIndex
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) :
    joint.ResidualCupIndex :=
  ⟨joint.star.spine, joint.spine_mem_residualCupFamily⟩

/-- Pair every residual four-cup, not merely four sampled failures, with all
six disjoint four-caps. -/
structure FullResidualCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) where
  cell : ∀ cup : joint.ResidualCupIndex, ∀ j : Fin 6,
    CupCapFirstJointSplit578 tree cup.1 (joint.saturation.capAt j)

theorem exists_fullResidualCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) :
    Nonempty (FullResidualCupSixCapAddressMatrix578 joint tree) := by
  classical
  exact ⟨{
    cell := fun cup j ↦ Classical.choice
      (exists_cupCapFirstJointSplit578_general tree
        (joint.ledger.mem_residualCupFamily.mp cup.2).1
        (joint.saturation.capAt_mem j))
  }⟩

/-- Every row of the full residual-family matrix is a prefix chain. -/
theorem FullResidualCupSixCapAddressMatrix578.row_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : FullResidualCupSixCapAddressMatrix578 joint tree)
    (cup : joint.ResidualCupIndex) (j k : Fin 6) :
    (matrix.cell cup j).path <+: (matrix.cell cup k).path ∨
      (matrix.cell cup k).path <+: (matrix.cell cup j).path := by
  have hcupData := mem_capWitnesses.mp
    (joint.ledger.mem_residualCupFamily.mp cup.2).1
  have hcupCard : 2 ≤ cup.1.card := by rw [hcupData.2.1]; omega
  let cupPath := tree.lowestSeparatingPath hcupData.1 hcupCard
  have hprefix (column : Fin 6) :
      (matrix.cell cup column).path <+: cupPath := by
    have hcapData := mem_capWitnesses.mp
      (joint.saturation.capAt_mem column)
    have hunionSub : cup.1 ∪ joint.saturation.capAt column ⊆ support :=
      Finset.union_subset hcupData.1 hcapData.1
    have hunionCard : 2 ≤
        (cup.1 ∪ joint.saturation.capAt column).card := by
      have hle := Finset.card_le_card
        (Finset.subset_union_left : cup.1 ⊆
          cup.1 ∪ joint.saturation.capAt column)
      rw [hcupData.2.1] at hle
      omega
    have hp := tree.lowestSeparatingPath_prefix_of_subset
      hcupData.1 hunionSub hcupCard hunionCard Finset.subset_union_left
    have hpathEq := (matrix.cell cup column).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard
    rw [hpathEq]
    exact hp
  exact List.prefix_or_prefix_of_prefix (hprefix j) (hprefix k)

/-- Every six-cap column of the full residual-family matrix is also a prefix
chain. -/
theorem FullResidualCupSixCapAddressMatrix578.column_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : FullResidualCupSixCapAddressMatrix578 joint tree)
    (first second : joint.ResidualCupIndex) (j : Fin 6) :
    (matrix.cell first j).path <+: (matrix.cell second j).path ∨
      (matrix.cell second j).path <+: (matrix.cell first j).path := by
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hcapCard : 2 ≤ (joint.saturation.capAt j).card := by
    rw [hcapData.2.1]
    omega
  let capPath := tree.lowestSeparatingPath hcapData.1 hcapCard
  have hprefix (cup : joint.ResidualCupIndex) :
      (matrix.cell cup j).path <+: capPath := by
    have hcupData := mem_capWitnesses.mp
      (joint.ledger.mem_residualCupFamily.mp cup.2).1
    have hunionSub : cup.1 ∪ joint.saturation.capAt j ⊆ support :=
      Finset.union_subset hcupData.1 hcapData.1
    have hunionCard : 2 ≤ (cup.1 ∪ joint.saturation.capAt j).card := by
      have hle := Finset.card_le_card
        (Finset.subset_union_right : joint.saturation.capAt j ⊆
          cup.1 ∪ joint.saturation.capAt j)
      rw [hcapData.2.1] at hle
      omega
    have hp := tree.lowestSeparatingPath_prefix_of_subset
      hcapData.1 hunionSub hcapCard hunionCard Finset.subset_union_right
    have hpathEq := (matrix.cell cup j).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard
    rw [hpathEq]
    exact hp
  exact List.prefix_or_prefix_of_prefix (hprefix first) (hprefix second)

/-- Row/column prefix chains over any two nonempty finite index types have a
global minimum. -/
theorem exists_globalPrefixMinimum_finiteMatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (path : ι → κ → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j) :
    ∃ i₀ j₀, ∀ i j, path i₀ j₀ <+: path i j := by
  classical
  obtain ⟨cell, _, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset ι).product (Finset.univ : Finset κ))
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

/-- A global common minimum for the full residual-family matrix. -/
structure FullResidualCupSixCapCommonMinimum578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : FullResidualCupSixCapAddressMatrix578 joint tree) where
  row : joint.ResidualCupIndex
  column : Fin 6
  minimal : ∀ cup j, (matrix.cell row column).path <+:
    (matrix.cell cup j).path

theorem FullResidualCupSixCapAddressMatrix578.commonMinimum_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : FullResidualCupSixCapAddressMatrix578 joint tree) :
    Nonempty (FullResidualCupSixCapCommonMinimum578 matrix) := by
  classical
  letI : Fintype (Finset (Fin n)) := Finset.fintype
  letI : Fintype joint.ResidualCupIndex := Subtype.fintype _
  letI : Nonempty joint.ResidualCupIndex := ⟨joint.spineResidualIndex⟩
  obtain ⟨row, column, hminimal⟩ := exists_globalPrefixMinimum_finiteMatrix
    (fun cup j ↦ (matrix.cell cup j).path)
    matrix.row_paths_comparable matrix.column_paths_comparable
  exact ⟨{ row := row, column := column, minimal := hminimal }⟩

/-- If strict cells occur in both directions below the full-family minimum,
every cell of the distinguished spine row remains at that minimum. -/
theorem FullResidualCupSixCapCommonMinimum578.spineRow_eq_base_of_oppositeExtensions
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1)
    {leftCup rightCup : joint.ResidualCupIndex}
    {leftColumn rightColumn : Fin 6}
    {leftTail rightTail : List Bool}
    (hleft : (matrix.cell leftCup leftColumn).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: leftTail)
    (hright : (matrix.cell rightCup rightColumn).path =
      (matrix.cell minimum.row minimum.column).path ++ true :: rightTail) :
    ∀ j, (matrix.cell joint.spineResidualIndex j).path =
      (matrix.cell minimum.row minimum.column).path := by
  intro j
  let base := (matrix.cell minimum.row minimum.column).path
  rcases list_eq_or_exists_firstStep_of_prefix
      (minimum.minimal joint.spineResidualIndex j) with
    heq | ⟨direction, tail, hstep⟩
  · exact heq
  · cases direction with
    | false =>
        have hmeet := joint.residualCup_meets_spine_of_card_eq_one
          hone rightCup.2
        exact (cupRows_not_opposite_of_inter'
          (matrix.cell rightCup rightColumn)
          (matrix.cell joint.spineResidualIndex j) hmeet
          (matrix.cell minimum.row minimum.column).lookup hright
          (by simpa [base] using hstep)).elim
    | true =>
        have hmeet := joint.residualCup_meets_spine_of_card_eq_one
          hone leftCup.2
        exact (cupRows_not_opposite_of_inter
          (matrix.cell leftCup leftColumn)
          (matrix.cell joint.spineResidualIndex j) hmeet
          (matrix.cell minimum.row minimum.column).lookup hleft
          (by simpa [base] using hstep)).elim

/-- Exhaustive full-family classification at the common minimum: all strict
extensions are one-sided, or opposite extensions force the complete
distinguished spine row to remain on the minimum address. -/
theorem FullResidualCupSixCapCommonMinimum578.oneSided_or_spinePlateau
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    (∀ cup j,
      (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ∨
        ∃ tail, (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: tail) ∨
    (∀ cup j,
      (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ∨
        ∃ tail, (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: tail) ∨
    (∀ j, (matrix.cell joint.spineResidualIndex j).path =
      (matrix.cell minimum.row minimum.column).path) := by
  let base := (matrix.cell minimum.row minimum.column).path
  by_cases hfalse : ∃ cup j tail,
      (matrix.cell cup j).path = base ++ false :: tail
  · by_cases htrue : ∃ cup j tail,
        (matrix.cell cup j).path = base ++ true :: tail
    · rcases hfalse with ⟨leftCup, leftColumn, leftTail, hleft⟩
      rcases htrue with ⟨rightCup, rightColumn, rightTail, hright⟩
      exact Or.inr (Or.inr
        (minimum.spineRow_eq_base_of_oppositeExtensions hone hleft hright))
    · right
      left
      intro cup j
      rcases list_eq_or_exists_firstStep_of_prefix
          (minimum.minimal cup j) with heq | ⟨direction, tail, hstep⟩
      · exact Or.inl heq
      · cases direction with
        | false => exact Or.inr ⟨tail, hstep⟩
        | true => exact (htrue ⟨cup, j, tail, by simpa [base] using hstep⟩).elim
  · left
    intro cup j
    rcases list_eq_or_exists_firstStep_of_prefix
        (minimum.minimal cup j) with heq | ⟨direction, tail, hstep⟩
    · exact Or.inl heq
    · cases direction with
      | false => exact (hfalse ⟨cup, j, tail, by simpa [base] using hstep⟩).elim
      | true => exact Or.inr ⟨tail, hstep⟩

/-! ## Reconnection to the exact 32-vertex gate -/

/-- The exact singleton-root gate now supplies the complete residual-family
matrix and a global common minimum, rather than only four sampled rows. -/
theorem exists_fourthDisjointCup_or_twoFullSpines_or_fullResidualCommonMinimum_at_32
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
        ∃ tree : DecompositionTree χ reservoir,
          ∃ matrix : FullResidualCupSixCapAddressMatrix578 joint tree,
            Nonempty (FullResidualCupSixCapCommonMinimum578 matrix)) := by
  rcases exists_fourthDisjointCup_or_twoFullSpines_or_residualAddressMatrix_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | ⟨joint, hmany | htight⟩
  · exact Or.inl hfourth
  · exact Or.inr ⟨joint, Or.inl hmany⟩
  · rcases htight with ⟨hone, ledger, tree, _⟩
    obtain ⟨matrix⟩ := exists_fullResidualCupSixCapAddressMatrix578 joint tree
    exact Or.inr ⟨joint, Or.inr ⟨hone, tree, matrix,
      matrix.commonMinimum_nonempty⟩⟩

end ErdosSzekeres

end
