module

public import ErdosSzekeres.StructuralChargingNextState578CarrierMatrix

@[expose] public section

/-!
# The decomposable eight-vertex four-cup obstruction

This file attacks the local obstruction isolated by the full residual-family
matrix at state `(5,7,8)`.  The first layer is certificate-free: if the lower
child of an eight-vertex deep-below split has at most three vertices, density
of four-cups on every five-subset already forces a five-cup.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

private theorem card_eq_lowerInter_add_upperInter_of_subset_union
    {n : ℕ} {s lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper) (hsub : s ⊆ lower ∪ upper) :
    s.card = (s ∩ lower).card + (s ∩ upper).card := by
  have hpartition : (s ∩ lower) ∪ (s ∩ upper) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases Finset.mem_union.mp (hsub hx) with hxLower | hxUpper
      · exact Or.inl ⟨hx, hxLower⟩
      · exact Or.inr ⟨hx, hxUpper⟩
  calc
    s.card = ((s ∩ lower) ∪ (s ∩ upper)).card :=
      congrArg Finset.card hpartition.symm
    _ = (s ∩ lower).card + (s ∩ upper).card :=
      Finset.card_union_of_disjoint
        (hdisjoint.mono Finset.inter_subset_right Finset.inter_subset_right)

/-! ## Small-lower root profiles -/

/-- A non-cup on at least four vertices has a non-cup four-subset.  This is
the elementary witness-extraction step used in the small-lower profiles. -/
theorem exists_four_subset_not_isCupSet_of_not_isCupSet
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hcard : 4 ≤ s.card) (hnotCup : ¬IsCupSet χ s) :
    ∃ four : Finset (Fin n),
      four ⊆ s ∧ four.card = 4 ∧ ¬IsCupSet χ four := by
  classical
  rw [IsCupSet] at hnotCup
  push Not at hnotCup
  obtain ⟨triple, hi, hj, hk, hcolor⟩ := hnotCup
  let tripleSet : Finset (Fin n) := {triple.i, triple.j, triple.k}
  have htripleSub : tripleSet ⊆ s := by
    intro x hx
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  have htripleCard : tripleSet.card = 3 := by
    simp [tripleSet, ne_of_lt triple.hij, ne_of_lt triple.hjk,
      ne_of_lt (triple.hij.trans triple.hjk)]
  have hrestNonempty : (s \ tripleSet).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset htripleSub, htripleCard]
    omega
  obtain ⟨x, hxRest⟩ := hrestNonempty
  let four := insert x tripleSet
  have hxS : x ∈ s := (Finset.mem_sdiff.mp hxRest).1
  have hxNotTriple : x ∉ tripleSet := (Finset.mem_sdiff.mp hxRest).2
  refine ⟨four, Finset.insert_subset hxS htripleSub, ?_, ?_⟩
  · simp [four, Finset.card_insert_of_notMem hxNotTriple, htripleCard]
  · intro hfourCup
    apply hcolor
    exact hfourCup triple (by simp [four, tripleSet])
      (by simp [four, tripleSet]) (by simp [four, tripleSet])

/-- For an eight-vertex deep-below split with at most three lower vertices,
four-cup density on five-subsets forces a five-cup.  The proof selects a
non-cup four-set in the upper child and adjoins one lower vertex.  Any
four-cup in the resulting five-set would have three upper vertices, which is
impossible for a cup crossing a deep-below split. -/
theorem deepSplit_smallLower_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcard : (lower ∪ upper).card = 8)
    (hlowerNonempty : lower.Nonempty)
    (hlowerCard : lower.card ≤ 3)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  classical
  by_contra hnoCupFive
  have hupperCard : 5 ≤ upper.card := by
    rw [Finset.card_union_of_disjoint hdeep.disjoint] at hcard
    omega
  obtain ⟨upperFive, hupperFiveSub, hupperFiveCard⟩ :=
    Finset.exists_subset_card_eq hupperCard
  have hupperFiveNotCup : ¬IsCupSet χ upperFive := by
    intro hcup
    exact hnoCupFive ⟨upperFive,
      hupperFiveSub.trans Finset.subset_union_right, hupperFiveCard, hcup⟩
  obtain ⟨four, hfourSub, hfourCard, hfourNotCup⟩ :=
    exists_four_subset_not_isCupSet_of_not_isCupSet
      (show 4 ≤ upperFive.card by omega) hupperFiveNotCup
  obtain ⟨q, hqLower⟩ := hlowerNonempty
  let five := insert q four
  have hfourUpper : four ⊆ upper := hfourSub.trans hupperFiveSub
  have hqNotFour : q ∉ four := by
    intro hqFour
    exact (Finset.disjoint_left.mp hdeep.disjoint) hqLower (hfourUpper hqFour)
  have hfiveSub : five ⊆ lower ∪ upper := by
    exact Finset.insert_subset (Finset.mem_union_left _ hqLower)
      (hfourUpper.trans Finset.subset_union_right)
  have hfiveCard : five.card = 5 := by
    simp [five, Finset.card_insert_of_notMem hqNotFour, hfourCard]
  obtain ⟨cup, hcupMem, hcupSubFive⟩ := hdense five hfiveSub hfiveCard
  have hcupData := mem_capWitnesses.mp hcupMem
  have hcupSet : IsCupSet χ cup := isCapSet_dual_iff.mp hcupData.2.2
  have hqCup : q ∈ cup := by
    by_contra hqNotCup
    have hcupSubFour : cup ⊆ four := by
      intro x hxCup
      rcases Finset.mem_insert.mp (hcupSubFive hxCup) with rfl | hxFour
      · exact (hqNotCup hxCup).elim
      · exact hxFour
    have hcupEq : cup = four := by
      apply (Finset.subset_iff_eq_of_card_le ?_).mp hcupSubFour
      rw [hfourCard, hcupData.2.1]
    exact hfourNotCup (hcupEq ▸ hcupSet)
  have hcupLower : (cup ∩ lower).Nonempty :=
    ⟨q, Finset.mem_inter.mpr ⟨hqCup, hqLower⟩⟩
  have heraseSub : cup.erase q ⊆ cup ∩ upper := by
    intro x hxErase
    have hxCup : x ∈ cup := (Finset.mem_erase.mp hxErase).2
    have hxNe : x ≠ q := (Finset.mem_erase.mp hxErase).1
    have hxFive := hcupSubFive hxCup
    rcases Finset.mem_insert.mp hxFive with hxq | hxFour
    · exact (hxNe hxq).elim
    · exact Finset.mem_inter.mpr ⟨hxCup, hfourUpper hxFour⟩
  have hthreeUpper : 3 ≤ (cup ∩ upper).card := by
    have hle := Finset.card_le_card heraseSub
    rw [Finset.card_erase_of_mem hqCup, hcupData.2.1] at hle
    omega
  have htwoUpper := hdeep.cup_inter_upper_card_le_two
    hcupData.1 hcupSet hcupLower
  omega

/-! ## The five-lower/three-upper root profile -/

/-- Five available lower vertices contain a lower four-cup under the dense
five-subset hypothesis.  This is the reusable internal witness for the
lower-heavy profiles. -/
theorem exists_lowerFourCup_of_five_le_card_of_denseFourCups
    {n : ℕ} {χ : TripleColoring n}
    {lower carrier : Finset (Fin n)}
    (hlowerSub : lower ⊆ carrier) (hlowerCard : 5 ≤ lower.card)
    (hdense : HasFourCupInEveryFiveSubset578 χ carrier) :
    ∃ cup : Finset (Fin n),
      cup ⊆ lower ∧ cup.card = 4 ∧ IsCupSet χ cup := by
  classical
  obtain ⟨five, hfiveSub, hfiveCard⟩ :=
    Finset.exists_subset_card_eq hlowerCard
  obtain ⟨cup, hcupMem, hcupSub⟩ :=
    hdense five (hfiveSub.trans hlowerSub) hfiveCard
  have hcupData := mem_capWitnesses.mp hcupMem
  exact ⟨cup, hcupSub.trans hfiveSub, hcupData.2.1,
    isCapSet_dual_iff.mp hcupData.2.2⟩

/-- Four-cup density restricts to a smaller carrier. -/
theorem HasFourCupInEveryFiveSubset578.mono
    {n : ℕ} {χ : TripleColoring n}
    {small carrier : Finset (Fin n)}
    (hdense : HasFourCupInEveryFiveSubset578 χ carrier)
    (hsmall : small ⊆ carrier) :
    HasFourCupInEveryFiveSubset578 χ small := by
  intro five hfiveSub hfiveCard
  obtain ⟨cup, hcupMem, hcupSub⟩ :=
    hdense five (hfiveSub.trans hsmall) hfiveCard
  have hcupData := mem_capWitnesses.mp hcupMem
  refine ⟨cup, mem_capWitnesses.mpr ⟨hcupSub.trans hfiveSub,
    hcupData.2⟩, hcupSub⟩

/-- In the `5+3` root profile, a lower four-cup cannot coexist with both
five-subset density and the absence of a five-cup.  The three upper vertices
all lie strictly between the two sweep endpoints of the lower cup.  Density
on those three vertices plus the two endpoints would require a crossing cup
whose upper member is simultaneously interior and a sweep endpoint. -/
theorem deepSplit_upperThree_lowerFourCup_dense_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cup : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hupperCard : upper.card = 3)
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = 4)
    (hcup : IsCupSet χ cup)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  classical
  by_contra hnoCupFive
  have hcupNonempty : cup.Nonempty := Finset.card_pos.mp (by omega)
  let a := cup.min' hcupNonempty
  let d := cup.max' hcupNonempty
  have haCup : a ∈ cup := by
    exact Finset.min'_mem cup hcupNonempty
  have hdCup : d ∈ cup := by
    exact Finset.max'_mem cup hcupNonempty
  have had : a ≠ d := by
    intro had
    have hcupSingleton : cup ⊆ {a} := by
      intro x hxCup
      simp only [Finset.mem_singleton]
      apply le_antisymm
      · have hxd : x ≤ d := Finset.le_max' cup x hxCup
        simpa [had] using hxd
      · exact Finset.min'_le cup x hxCup
    have hcardLe := Finset.card_le_card hcupSingleton
    simp only [Finset.card_singleton] at hcardLe
    omega
  have haLower : a ∈ lower := hcupSub haCup
  have hdLower : d ∈ lower := hcupSub hdCup
  have haNotUpper : a ∉ upper := fun haUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) haLower haUpper
  have hdNotUpper : d ∉ upper := fun hdUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) hdLower hdUpper
  have hupperInterior {q : Fin n} (hqUpper : q ∈ upper) : a < q ∧ q < d := by
    have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint cup q := by
      intro hendpoint
      exact hnoCupFive (hdeep.containsCupSet_succ_of_upper_endpoint
        hcupSub hcupCard hcup hqUpper hendpoint)
    rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
      at hnotEndpoint
    obtain ⟨⟨x, hxCup, hxq⟩, ⟨y, hyCup, hqy⟩⟩ := hnotEndpoint
    exact ⟨lt_of_le_of_lt (Finset.min'_le cup x hxCup) hxq,
      lt_of_lt_of_le hqy (Finset.le_max' cup y hyCup)⟩
  let five := insert a (insert d upper)
  have hfiveSub : five ⊆ lower ∪ upper := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_union_left _ haLower
    rcases Finset.mem_insert.mp hx with rfl | hxUpper
    · exact Finset.mem_union_left _ hdLower
    · exact Finset.mem_union_right _ hxUpper
  have hfiveCard : five.card = 5 := by
    simp [five, Finset.card_insert_of_notMem, haNotUpper, hdNotUpper, had,
      hupperCard]
  obtain ⟨crossingCup, hcrossingMem, hcrossingSubFive⟩ :=
    hdense five hfiveSub hfiveCard
  have hcrossingData := mem_capWitnesses.mp hcrossingMem
  have hcrossingSub : crossingCup ⊆ lower ∪ upper :=
    hcrossingData.1
  have hcrossingCup : IsCupSet χ crossingCup :=
    isCapSet_dual_iff.mp hcrossingData.2.2
  have hcrossingLowerSub : crossingCup ∩ lower ⊆ {a, d} := by
    intro x hx
    have hxCup := (Finset.mem_inter.mp hx).1
    have hxLower := (Finset.mem_inter.mp hx).2
    rcases Finset.mem_insert.mp (hcrossingSubFive hxCup) with hxa | hx
    · simp [hxa]
    rcases Finset.mem_insert.mp hx with hxd | hxUpper
    · simp [hxd]
    · exact (Finset.disjoint_left.mp hdeep.disjoint hxLower hxUpper).elim
  have hcrossingLowerCard : (crossingCup ∩ lower).card ≤ 2 := by
    have hle := Finset.card_le_card hcrossingLowerSub
    simpa [had] using hle
  have hcrossingLower : (crossingCup ∩ lower).Nonempty := by
    by_contra hempty
    have hzero : (crossingCup ∩ lower).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hempty ▸ rfl
    have hpartition := card_eq_lowerInter_add_upperInter_of_subset_union
      hdeep.disjoint hcrossingSub
    have hupperLe := Finset.card_le_card
      (show crossingCup ∩ upper ⊆ upper from Finset.inter_subset_right)
    rw [hcrossingData.2.1, hzero] at hpartition
    rw [hupperCard] at hupperLe
    omega
  have hcrossingUpperCard := hdeep.cup_inter_upper_card_le_two
    hcrossingSub hcrossingCup hcrossingLower
  have hpartition := card_eq_lowerInter_add_upperInter_of_subset_union
    hdeep.disjoint hcrossingSub
  have hlowerEq : (crossingCup ∩ lower).card = 2 := by
    rw [hcrossingData.2.1] at hpartition
    omega
  have hupperEq : (crossingCup ∩ upper).card = 2 := by
    rw [hcrossingData.2.1] at hpartition
    omega
  have hcrossingLowerEq : crossingCup ∩ lower = {a, d} := by
    apply (Finset.subset_iff_eq_of_card_le ?_).mp hcrossingLowerSub
    simp [hlowerEq, had]
  have haCrossing : a ∈ crossingCup := by
    have : a ∈ crossingCup ∩ lower := by
      rw [hcrossingLowerEq]
      simp
    exact (Finset.mem_inter.mp this).1
  have hdCrossing : d ∈ crossingCup := by
    have : d ∈ crossingCup ∩ lower := by
      rw [hcrossingLowerEq]
      simp
    exact (Finset.mem_inter.mp this).1
  obtain ⟨q, hqInter⟩ :=
    Finset.card_pos.mp (show 0 < (crossingCup ∩ upper).card by omega)
  have hqCrossing := (Finset.mem_inter.mp hqInter).1
  have hqUpper := (Finset.mem_inter.mp hqInter).2
  have hendpoint := hdeep.upper_mem_cup_isSweepEndpoint
    hcrossingSub hcrossingCup hcrossingLower hqCrossing hqUpper
  have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint crossingCup q := by
    rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
    exact ⟨⟨a, haCrossing, (hupperInterior hqUpper).1⟩,
      ⟨d, hdCrossing, (hupperInterior hqUpper).2⟩⟩
  exact hnotEndpoint hendpoint

/-- The complete `5+3` root profile. -/
theorem deepSplit_lowerFive_upperThree_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 5) (hupperCard : upper.card = 3)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  obtain ⟨cup, hcupSub, hcupCard, hcup⟩ :=
    exists_lowerFourCup_of_five_le_card_of_denseFourCups
      Finset.subset_union_left (by omega) hdense
  exact deepSplit_upperThree_lowerFourCup_dense_force_cupFive hdeep
    hupperCard hcupSub hcupCard hcup hdense

/-! ## The six-lower/two-upper root profile -/

/-- The analogous endpoint trap for two upper vertices.  A fifth test set now
uses the two endpoints and one additional lower-cup vertex.  If its forced
four-cup omits one endpoint, then it must use both upper vertices; the nearer
upper vertex is trapped between the retained endpoint and the other upper
vertex. -/
theorem deepSplit_upperTwo_lowerFourCup_dense_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cup : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hupperCard : upper.card = 2)
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = 4)
    (hcup : IsCupSet χ cup)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  classical
  by_contra hnoCupFive
  have hcupNonempty : cup.Nonempty := Finset.card_pos.mp (by omega)
  let a := cup.min' hcupNonempty
  let d := cup.max' hcupNonempty
  have haCup : a ∈ cup := Finset.min'_mem cup hcupNonempty
  have hdCup : d ∈ cup := Finset.max'_mem cup hcupNonempty
  have had : a ≠ d := by
    intro had
    have hcupSingleton : cup ⊆ {a} := by
      intro y hyCup
      simp only [Finset.mem_singleton]
      apply le_antisymm
      · have hyd : y ≤ d := Finset.le_max' cup y hyCup
        simpa [had] using hyd
      · exact Finset.min'_le cup y hyCup
    have hcardLe := Finset.card_le_card hcupSingleton
    simp only [Finset.card_singleton] at hcardLe
    omega
  have hpairSub : {a, d} ⊆ cup := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact haCup
    · exact hdCup
  have hrestCard : (cup \ {a, d}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub, hcupCard]
    simp [had]
  obtain ⟨x, hxRest⟩ :=
    Finset.card_pos.mp (show 0 < (cup \ {a, d}).card by omega)
  have hxCup : x ∈ cup := (Finset.mem_sdiff.mp hxRest).1
  have hxNotPair : x ∉ {a, d} := (Finset.mem_sdiff.mp hxRest).2
  have hxa : x ≠ a := by
    intro hxa
    exact hxNotPair (by simp [hxa])
  have hxd : x ≠ d := by
    intro hxd
    exact hxNotPair (by simp [hxd])
  have haLower : a ∈ lower := hcupSub haCup
  have hdLower : d ∈ lower := hcupSub hdCup
  have hxLower : x ∈ lower := hcupSub hxCup
  have haNotUpper : a ∉ upper := fun haUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) haLower haUpper
  have hdNotUpper : d ∉ upper := fun hdUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) hdLower hdUpper
  have hxNotUpper : x ∉ upper := fun hxUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) hxLower hxUpper
  have hupperInterior {q : Fin n} (hqUpper : q ∈ upper) : a < q ∧ q < d := by
    have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint cup q := by
      intro hendpoint
      exact hnoCupFive (hdeep.containsCupSet_succ_of_upper_endpoint
        hcupSub hcupCard hcup hqUpper hendpoint)
    rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
      at hnotEndpoint
    obtain ⟨⟨y, hyCup, hyq⟩, ⟨z, hzCup, hqz⟩⟩ := hnotEndpoint
    exact ⟨lt_of_le_of_lt (Finset.min'_le cup y hyCup) hyq,
      lt_of_lt_of_le hqz (Finset.le_max' cup z hzCup)⟩
  let five := insert a (insert d (insert x upper))
  have hfiveSub : five ⊆ lower ∪ upper := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union_left _ haLower
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union_left _ hdLower
    rcases Finset.mem_insert.mp hy with rfl | hyUpper
    · exact Finset.mem_union_left _ hxLower
    · exact Finset.mem_union_right _ hyUpper
  have hfiveCard : five.card = 5 := by
    have haNotRest : a ∉ insert d (insert x upper) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨had, hxa.symm, haNotUpper⟩
    have hdNotRest : d ∉ insert x upper := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hxd.symm, hdNotUpper⟩
    simp only [five, Finset.card_insert_of_notMem haNotRest,
      Finset.card_insert_of_notMem hdNotRest,
      Finset.card_insert_of_notMem hxNotUpper, hupperCard]
  obtain ⟨crossingCup, hcrossingMem, hcrossingSubFive⟩ :=
    hdense five hfiveSub hfiveCard
  have hcrossingData := mem_capWitnesses.mp hcrossingMem
  have hcrossingSub : crossingCup ⊆ lower ∪ upper := hcrossingData.1
  have hcrossingCup : IsCupSet χ crossingCup :=
    isCapSet_dual_iff.mp hcrossingData.2.2
  have hcrossingLowerSub : crossingCup ∩ lower ⊆ {a, d, x} := by
    intro y hy
    have hyCup := (Finset.mem_inter.mp hy).1
    have hyLower := (Finset.mem_inter.mp hy).2
    rcases Finset.mem_insert.mp (hcrossingSubFive hyCup) with hya | hy
    · simp [hya]
    rcases Finset.mem_insert.mp hy with hyd | hy
    · simp [hyd]
    rcases Finset.mem_insert.mp hy with hyx | hyUpper
    · simp [hyx]
    · exact (Finset.disjoint_left.mp hdeep.disjoint hyLower hyUpper).elim
  have hcrossingLowerCard : (crossingCup ∩ lower).card ≤ 3 := by
    have hle := Finset.card_le_card hcrossingLowerSub
    have htripleCard : ({a, d, x} : Finset (Fin n)).card = 3 := by
      have haNotRest : a ∉ ({d, x} : Finset (Fin n)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨had, hxa.symm⟩
      have hdNotX : d ∉ ({x} : Finset (Fin n)) := by
        simpa using hxd.symm
      simp only [Finset.card_insert_of_notMem haNotRest,
        Finset.card_insert_of_notMem hdNotX, Finset.card_singleton]
    omega
  have hpartition := card_eq_lowerInter_add_upperInter_of_subset_union
    hdeep.disjoint hcrossingSub
  have hcrossingLower : (crossingCup ∩ lower).Nonempty := by
    apply Finset.card_pos.mp
    have hupperLe := Finset.card_le_card
      (show crossingCup ∩ upper ⊆ upper from Finset.inter_subset_right)
    rw [hcrossingData.2.1] at hpartition
    rw [hupperCard] at hupperLe
    omega
  have hcrossingUpper : (crossingCup ∩ upper).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcrossingData.2.1] at hpartition
    omega
  have hcrossingUpperCard := hdeep.cup_inter_upper_card_le_two
    hcrossingSub hcrossingCup hcrossingLower
  have hlowerAtLeastTwo : 2 ≤ (crossingCup ∩ lower).card := by
    rw [hcrossingData.2.1] at hpartition
    omega
  by_cases haCrossing : a ∈ crossingCup
  · by_cases hdCrossing : d ∈ crossingCup
    · obtain ⟨q, hqInter⟩ := hcrossingUpper
      have hqCrossing := (Finset.mem_inter.mp hqInter).1
      have hqUpper := (Finset.mem_inter.mp hqInter).2
      have hendpoint := hdeep.upper_mem_cup_isSweepEndpoint
        hcrossingSub hcrossingCup hcrossingLower hqCrossing hqUpper
      have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint crossingCup q := by
        rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
        exact ⟨⟨a, haCrossing, (hupperInterior hqUpper).1⟩,
          ⟨d, hdCrossing, (hupperInterior hqUpper).2⟩⟩
      exact hnotEndpoint hendpoint
    · have hlowerReduced : crossingCup ∩ lower ⊆ {a, x} := by
        intro y hy
        have hyTriple := hcrossingLowerSub hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyTriple ⊢
        rcases hyTriple with hya | hyd | hyx
        · exact Or.inl hya
        · exact (hdCrossing ((hyd ▸ Finset.mem_inter.mp hy).1)).elim
        · exact Or.inr hyx
      have hlowerLeTwo : (crossingCup ∩ lower).card ≤ 2 := by
        have hle := Finset.card_le_card hlowerReduced
        have hpairCard : ({a, x} : Finset (Fin n)).card = 2 := by
          have haNotX : a ∉ ({x} : Finset (Fin n)) := by
            simpa using hxa.symm
          simp only [Finset.card_insert_of_notMem haNotX,
            Finset.card_singleton]
        omega
      have hupperEq : (crossingCup ∩ upper).card = 2 := by
        rw [hcrossingData.2.1] at hpartition
        omega
      let e : Fin 2 ↪o Fin n :=
        (crossingCup ∩ upper).orderEmbOfFin hupperEq
      let q := e 0
      let r := e 1
      have hqr : q < r := e.strictMono (by decide)
      have hqInter : q ∈ crossingCup ∩ upper :=
        (crossingCup ∩ upper).orderEmbOfFin_mem hupperEq 0
      have hrInter : r ∈ crossingCup ∩ upper :=
        (crossingCup ∩ upper).orderEmbOfFin_mem hupperEq 1
      have hendpoint := hdeep.upper_mem_cup_isSweepEndpoint
        hcrossingSub hcrossingCup hcrossingLower
        (Finset.mem_inter.mp hqInter).1 (Finset.mem_inter.mp hqInter).2
      have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint crossingCup q := by
        rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
        exact ⟨⟨a, haCrossing, (hupperInterior
          (Finset.mem_inter.mp hqInter).2).1⟩,
          ⟨r, (Finset.mem_inter.mp hrInter).1, hqr⟩⟩
      exact hnotEndpoint hendpoint
  · have hlowerReduced : crossingCup ∩ lower ⊆ {d, x} := by
      intro y hy
      have hyTriple := hcrossingLowerSub hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyTriple ⊢
      rcases hyTriple with hya | hyd | hyx
      · exact (haCrossing ((hya ▸ Finset.mem_inter.mp hy).1)).elim
      · exact Or.inl hyd
      · exact Or.inr hyx
    have hlowerEq : crossingCup ∩ lower = {d, x} := by
      apply (Finset.subset_iff_eq_of_card_le ?_).mp hlowerReduced
      have hle := Finset.card_le_card hlowerReduced
      have hpairCard : ({d, x} : Finset (Fin n)).card = 2 := by
        have hdNotX : d ∉ ({x} : Finset (Fin n)) := by
          simpa using hxd.symm
        simp only [Finset.card_insert_of_notMem hdNotX,
          Finset.card_singleton]
      omega
    have hdCrossing : d ∈ crossingCup := by
      have : d ∈ crossingCup ∩ lower := by
        rw [hlowerEq]
        simp
      exact (Finset.mem_inter.mp this).1
    have hlowerEqTwo : (crossingCup ∩ lower).card = 2 := by
      rw [hlowerEq]
      have hdNotX : d ∉ ({x} : Finset (Fin n)) := by
        simpa using hxd.symm
      simp only [Finset.card_insert_of_notMem hdNotX,
        Finset.card_singleton]
    have hupperEq : (crossingCup ∩ upper).card = 2 := by
      rw [hcrossingData.2.1, hlowerEqTwo] at hpartition
      omega
    let e : Fin 2 ↪o Fin n :=
      (crossingCup ∩ upper).orderEmbOfFin hupperEq
    let q := e 0
    let r := e 1
    have hqr : q < r := e.strictMono (by decide)
    have hqInter : q ∈ crossingCup ∩ upper :=
      (crossingCup ∩ upper).orderEmbOfFin_mem hupperEq 0
    have hrInter : r ∈ crossingCup ∩ upper :=
      (crossingCup ∩ upper).orderEmbOfFin_mem hupperEq 1
    have hendpoint := hdeep.upper_mem_cup_isSweepEndpoint
      hcrossingSub hcrossingCup hcrossingLower
      (Finset.mem_inter.mp hrInter).1 (Finset.mem_inter.mp hrInter).2
    have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint crossingCup r := by
      rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
      exact ⟨⟨q, (Finset.mem_inter.mp hqInter).1, hqr⟩,
        ⟨d, hdCrossing, (hupperInterior
          (Finset.mem_inter.mp hrInter).2).2⟩⟩
    exact hnotEndpoint hendpoint

/-- The complete `6+2` root profile. -/
theorem deepSplit_lowerSix_upperTwo_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 6) (hupperCard : upper.card = 2)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  obtain ⟨cup, hcupSub, hcupCard, hcup⟩ :=
    exists_lowerFourCup_of_five_le_card_of_denseFourCups
      Finset.subset_union_left (by omega) hdense
  exact deepSplit_upperTwo_lowerFourCup_dense_force_cupFive hdeep
    hupperCard hcupSub hcupCard hcup hdense

/-! ## The balanced four/four root profile -/

/-- In a balanced root, density first forces an upper pair bracketing the
entire lower child.  A lower cup triple then joins that pair to form the
forbidden five-cup. -/
theorem deepSplit_lowerFour_upperFour_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 4) (hupperCard : upper.card = 4)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  classical
  by_contra hnoCupFive
  have hlowerNonempty : lower.Nonempty := Finset.card_pos.mp (by omega)
  have hupperThreeLe : 3 ≤ upper.card := by omega
  obtain ⟨upperThree, hupperThreeSub, hupperThreeCard⟩ :=
    Finset.exists_subset_card_eq hupperThreeLe
  have hrestrictedSub : lower ∪ upperThree ⊆ lower ∪ upper := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyLower | hyUpper
    · exact Finset.mem_union_left _ hyLower
    · exact Finset.mem_union_right _ (hupperThreeSub hyUpper)
  have hrestrictedDeep := hdeep.mono (show lower ⊆ lower from fun _ h => h)
    hupperThreeSub
  have hlowerNotCup : ¬IsCupSet χ lower := by
    intro hlowerCup
    have hcupFiveRestricted :=
      deepSplit_upperThree_lowerFourCup_dense_force_cupFive
        hrestrictedDeep hupperThreeCard
        (show lower ⊆ lower from fun _ h => h) hlowerCard hlowerCup
        (hdense.mono hrestrictedSub)
    exact hnoCupFive (FinsetPolygon.ContainsCupSet.mono
      hcupFiveRestricted hrestrictedSub)
  obtain ⟨u, huUpper⟩ := Finset.card_pos.mp (by omega : 0 < upper.card)
  have huNotLower : u ∉ lower := fun huLower =>
    (Finset.disjoint_left.mp hdeep.disjoint) huLower huUpper
  let lowerFive := insert u lower
  have hlowerFiveSub : lowerFive ⊆ lower ∪ upper := by
    exact Finset.insert_subset (Finset.mem_union_right _ huUpper)
      Finset.subset_union_left
  have hlowerFiveCard : lowerFive.card = 5 := by
    simp [lowerFive, Finset.card_insert_of_notMem huNotLower, hlowerCard]
  obtain ⟨lowerCrossingCup, hlowerCrossingMem, hlowerCrossingSubFive⟩ :=
    hdense lowerFive hlowerFiveSub hlowerFiveCard
  have hlowerCrossingData := mem_capWitnesses.mp hlowerCrossingMem
  have hlowerCrossingCup : IsCupSet χ lowerCrossingCup :=
    isCapSet_dual_iff.mp hlowerCrossingData.2.2
  have huCrossing : u ∈ lowerCrossingCup := by
    by_contra huNotCrossing
    have hsubLower : lowerCrossingCup ⊆ lower := by
      intro y hyCup
      rcases Finset.mem_insert.mp (hlowerCrossingSubFive hyCup) with hyu | hyLower
      · exact (huNotCrossing (hyu ▸ hyCup)).elim
      · exact hyLower
    have heqLower : lowerCrossingCup = lower := by
      apply (Finset.subset_iff_eq_of_card_le ?_).mp hsubLower
      rw [hlowerCard, hlowerCrossingData.2.1]
    exact hlowerNotCup (heqLower ▸ hlowerCrossingCup)
  let lowerTriple := lowerCrossingCup.erase u
  have hlowerTripleCard : lowerTriple.card = 3 := by
    simp [lowerTriple, Finset.card_erase_of_mem huCrossing,
      hlowerCrossingData.2.1]
  have hlowerTripleSub : lowerTriple ⊆ lower := by
    intro y hyTriple
    have hyCup := (Finset.mem_erase.mp hyTriple).2
    have hyNe := (Finset.mem_erase.mp hyTriple).1
    rcases Finset.mem_insert.mp (hlowerCrossingSubFive hyCup) with hyu | hyLower
    · exact (hyNe hyu).elim
    · exact hyLower
  have hlowerTripleCup : IsCupSet χ lowerTriple :=
    FinsetPolygon.IsCupSet.mono hlowerCrossingCup
      (Finset.erase_subset u lowerCrossingCup)
  let a := lower.min' hlowerNonempty
  let d := lower.max' hlowerNonempty
  have haLower : a ∈ lower := Finset.min'_mem lower hlowerNonempty
  have hdLower : d ∈ lower := Finset.max'_mem lower hlowerNonempty
  have had : a ≠ d := by
    intro had
    have hlowerSingleton : lower ⊆ {a} := by
      intro y hyLower
      simp only [Finset.mem_singleton]
      apply le_antisymm
      · have hyd : y ≤ d := Finset.le_max' lower y hyLower
        simpa [had] using hyd
      · exact Finset.min'_le lower y hyLower
    have hcardLe := Finset.card_le_card hlowerSingleton
    simp only [Finset.card_singleton] at hcardLe
    omega
  let bracketFive := insert a (insert d upperThree)
  have hbracketFiveSub : bracketFive ⊆ lower ∪ upper := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union_left _ haLower
    rcases Finset.mem_insert.mp hy with rfl | hyUpper
    · exact Finset.mem_union_left _ hdLower
    · exact Finset.mem_union_right _ (hupperThreeSub hyUpper)
  have haNotUpperThree : a ∉ upperThree := fun haUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) haLower (hupperThreeSub haUpper)
  have hdNotUpperThree : d ∉ upperThree := fun hdUpper =>
    (Finset.disjoint_left.mp hdeep.disjoint) hdLower (hupperThreeSub hdUpper)
  have hbracketFiveCard : bracketFive.card = 5 := by
    simp [bracketFive, Finset.card_insert_of_notMem, haNotUpperThree,
      hdNotUpperThree, had, hupperThreeCard]
  obtain ⟨bracketCup, hbracketMem, hbracketSubFive⟩ :=
    hdense bracketFive hbracketFiveSub hbracketFiveCard
  have hbracketData := mem_capWitnesses.mp hbracketMem
  have hbracketSub : bracketCup ⊆ lower ∪ upper := hbracketData.1
  have hbracketCup : IsCupSet χ bracketCup :=
    isCapSet_dual_iff.mp hbracketData.2.2
  have hbracketLowerSub : bracketCup ∩ lower ⊆ {a, d} := by
    intro y hy
    have hyCup := (Finset.mem_inter.mp hy).1
    have hyLower := (Finset.mem_inter.mp hy).2
    rcases Finset.mem_insert.mp (hbracketSubFive hyCup) with hya | hy
    · simp [hya]
    rcases Finset.mem_insert.mp hy with hyd | hyUpperThree
    · simp [hyd]
    · exact (Finset.disjoint_left.mp hdeep.disjoint hyLower
        (hupperThreeSub hyUpperThree)).elim
  have hbracketLowerCard : (bracketCup ∩ lower).card ≤ 2 := by
    have hle := Finset.card_le_card hbracketLowerSub
    simpa [had] using hle
  have hbracketLower : (bracketCup ∩ lower).Nonempty := by
    apply Finset.card_pos.mp
    have hupperThreeBound : bracketCup ∩ upper ⊆ upperThree := by
      intro y hy
      have hyCup := (Finset.mem_inter.mp hy).1
      have hyUpper := (Finset.mem_inter.mp hy).2
      rcases Finset.mem_insert.mp (hbracketSubFive hyCup) with hya | hy
      · exact (Finset.disjoint_left.mp hdeep.disjoint haLower
          (hya ▸ hyUpper)).elim
      rcases Finset.mem_insert.mp hy with hyd | hyUpperThree
      · exact (Finset.disjoint_left.mp hdeep.disjoint hdLower
          (hyd ▸ hyUpper)).elim
      · exact hyUpperThree
    have hupperLe := Finset.card_le_card hupperThreeBound
    have hpartition := card_eq_lowerInter_add_upperInter_of_subset_union
      hdeep.disjoint hbracketSub
    rw [hbracketData.2.1] at hpartition
    rw [hupperThreeCard] at hupperLe
    omega
  have hbracketUpperCard := hdeep.cup_inter_upper_card_le_two
    hbracketSub hbracketCup hbracketLower
  have hbracketPartition := card_eq_lowerInter_add_upperInter_of_subset_union
    hdeep.disjoint hbracketSub
  have hbracketLowerEqTwo : (bracketCup ∩ lower).card = 2 := by
    rw [hbracketData.2.1] at hbracketPartition
    omega
  have hbracketUpperEqTwo : (bracketCup ∩ upper).card = 2 := by
    rw [hbracketData.2.1] at hbracketPartition
    omega
  have hbracketLowerEq : bracketCup ∩ lower = {a, d} := by
    apply (Finset.subset_iff_eq_of_card_le ?_).mp hbracketLowerSub
    simp [hbracketLowerEqTwo, had]
  have haBracket : a ∈ bracketCup := by
    have : a ∈ bracketCup ∩ lower := by
      rw [hbracketLowerEq]
      simp
    exact (Finset.mem_inter.mp this).1
  have hdBracket : d ∈ bracketCup := by
    have : d ∈ bracketCup ∩ lower := by
      rw [hbracketLowerEq]
      simp
    exact (Finset.mem_inter.mp this).1
  let e : Fin 2 ↪o Fin n :=
    (bracketCup ∩ upper).orderEmbOfFin hbracketUpperEqTwo
  let qLeft := e 0
  let qRight := e 1
  have hqLeftRight : qLeft < qRight := e.strictMono (by decide)
  have hqLeftInter : qLeft ∈ bracketCup ∩ upper :=
    (bracketCup ∩ upper).orderEmbOfFin_mem hbracketUpperEqTwo 0
  have hqRightInter : qRight ∈ bracketCup ∩ upper :=
    (bracketCup ∩ upper).orderEmbOfFin_mem hbracketUpperEqTwo 1
  have hqLeftEndpoint := hdeep.upper_mem_cup_isSweepEndpoint
    hbracketSub hbracketCup hbracketLower
    (Finset.mem_inter.mp hqLeftInter).1 (Finset.mem_inter.mp hqLeftInter).2
  have hqRightEndpoint := hdeep.upper_mem_cup_isSweepEndpoint
    hbracketSub hbracketCup hbracketLower
    (Finset.mem_inter.mp hqRightInter).1 (Finset.mem_inter.mp hqRightInter).2
  have hqLeftLtA : qLeft < a := by
    rcases hqLeftEndpoint with hleft | hright
    · have hle := hleft a haBracket
      have hne : qLeft ≠ a := fun hEq =>
        (Finset.disjoint_left.mp hdeep.disjoint haLower
          (hEq ▸ (Finset.mem_inter.mp hqLeftInter).2))
      exact lt_of_le_of_ne hle hne
    · have hbad := hright qRight (Finset.mem_inter.mp hqRightInter).1
      exact (not_le_of_gt hqLeftRight hbad).elim
  have hdLtQRight : d < qRight := by
    rcases hqRightEndpoint with hleft | hright
    · have hbad := hleft qLeft (Finset.mem_inter.mp hqLeftInter).1
      exact (not_le_of_gt hqLeftRight hbad).elim
    · have hle := hright d hdBracket
      have hne : d ≠ qRight := fun hEq =>
        (Finset.disjoint_left.mp hdeep.disjoint hdLower
          (hEq ▸ (Finset.mem_inter.mp hqRightInter).2))
      exact lt_of_le_of_ne hle hne
  have hqLeftBelow {y : Fin n} (hyLower : y ∈ lower) : qLeft < y :=
    hqLeftLtA.trans_le (Finset.min'_le lower y hyLower)
  have hqRightAbove {y : Fin n} (hyLower : y ∈ lower) : y < qRight :=
    (Finset.le_max' lower y hyLower).trans_lt hdLtQRight
  let fiveCup := insert qLeft (insert qRight lowerTriple)
  have hqLeftNotLower : qLeft ∉ lower := fun hqLower =>
    (Finset.disjoint_left.mp hdeep.disjoint) hqLower
      (Finset.mem_inter.mp hqLeftInter).2
  have hqRightNotLower : qRight ∉ lower := fun hqLower =>
    (Finset.disjoint_left.mp hdeep.disjoint) hqLower
      (Finset.mem_inter.mp hqRightInter).2
  have hqLeftNotTriple : qLeft ∉ lowerTriple := fun hqTriple =>
    hqLeftNotLower (hlowerTripleSub hqTriple)
  have hqRightNotTriple : qRight ∉ lowerTriple := fun hqTriple =>
    hqRightNotLower (hlowerTripleSub hqTriple)
  have hfiveCupCard : fiveCup.card = 5 := by
    have hqLeftNeRight : qLeft ≠ qRight := ne_of_lt hqLeftRight
    simp [fiveCup, Finset.card_insert_of_notMem, hqLeftNotTriple,
      hqRightNotTriple, hqLeftNeRight, hlowerTripleCard]
  have hfiveCupSub : fiveCup ⊆ lower ∪ upper := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hqLeftInter).2
    rcases Finset.mem_insert.mp hy with rfl | hyTriple
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hqRightInter).2
    · exact Finset.mem_union_left _ (hlowerTripleSub hyTriple)
  have hfiveIsCup : IsCupSet χ fiveCup := by
    intro t hi hj hk
    by_cases hallTriple :
        t.i ∈ lowerTriple ∧ t.j ∈ lowerTriple ∧ t.k ∈ lowerTriple
    · exact hlowerTripleCup t hallTriple.1 hallTriple.2.1 hallTriple.2.2
    · have hiUnion := hfiveCupSub hi
      have hjUnion := hfiveCupSub hj
      have hkUnion := hfiveCupSub hk
      have hjLower : t.j ∈ lower := by
        rcases Finset.mem_insert.mp hj with hqLeft | hj
        · rcases Finset.mem_insert.mp hi with hiLeft | hi
          · exact (ne_of_lt t.hij (hiLeft.trans hqLeft.symm)).elim
          rcases Finset.mem_insert.mp hi with hiRight | hiTriple
          · have hbad : qRight < qLeft := by
              simpa [hiRight, hqLeft] using t.hij
            exact (not_lt_of_ge (le_of_lt hqLeftRight) hbad).elim
          · have hbad : t.i < qLeft := by simpa [hqLeft] using t.hij
            exact (not_lt_of_ge (le_of_lt (hqLeftBelow
              (hlowerTripleSub hiTriple))) hbad).elim
        rcases Finset.mem_insert.mp hj with hqRight | hjTriple
        · rcases Finset.mem_insert.mp hk with hkLeft | hk
          · have hbad : qRight < qLeft := by
              simpa [hqRight, hkLeft] using t.hjk
            exact (not_lt_of_ge (le_of_lt hqLeftRight) hbad).elim
          rcases Finset.mem_insert.mp hk with hkRight | hkTriple
          · exact (ne_of_lt t.hjk (hqRight.trans hkRight.symm)).elim
          · have hbad : qRight < t.k := by simpa [hqRight] using t.hjk
            exact (not_lt_of_ge (le_of_lt (hqRightAbove
              (hlowerTripleSub hkTriple))) hbad).elim
        · exact hlowerTripleSub hjTriple
      have hnotLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
        rintro ⟨hiLower, hjLower', hkLower⟩
        apply hallTriple
        constructor
        · rcases Finset.mem_insert.mp hi with hiLeft | hi
          · exact (hqLeftNotLower (hiLeft ▸ hiLower)).elim
          rcases Finset.mem_insert.mp hi with hiRight | hiTriple
          · exact (hqRightNotLower (hiRight ▸ hiLower)).elim
          · exact hiTriple
        constructor
        · rcases Finset.mem_insert.mp hj with hjLeft | hj
          · exact (hqLeftNotLower (hjLeft ▸ hjLower')).elim
          rcases Finset.mem_insert.mp hj with hjRight | hjTriple
          · exact (hqRightNotLower (hjRight ▸ hjLower')).elim
          · exact hjTriple
        · rcases Finset.mem_insert.mp hk with hkLeft | hk
          · exact (hqLeftNotLower (hkLeft ▸ hkLower)).elim
          rcases Finset.mem_insert.mp hk with hkRight | hkTriple
          · exact (hqRightNotLower (hkRight ▸ hkLower)).elim
          · exact hkTriple
      have hnotUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
        rintro ⟨_, hjUpper, _⟩
        exact (Finset.disjoint_left.mp hdeep.disjoint) hjLower hjUpper
      simpa [hjLower] using hdeep.crossing t hiUnion hjUnion hkUnion
        hnotLower hnotUpper
  exact hnoCupFive ⟨fiveCup, hfiveCupSub, hfiveCupCard, hfiveIsCup⟩

/-! ## The seven-lower/one-upper root profile -/

/-- A three-cup joined to a disjoint two-set is a five-cup whenever every
two-from-three plus the two-set is already a four-cup.  This small gluing
lemma is the internal combinatorial engine of the extreme `7+1` profile. -/
theorem isCupSet_union_three_two_of_all_two_two
    {n : ℕ} {χ : TripleColoring n}
    {three two : Finset (Fin n)}
    (hthreeCard : three.card = 3)
    (hthreeCup : IsCupSet χ three)
    (hallTwoTwo : ∀ leftTwo : Finset (Fin n),
      leftTwo ⊆ three → leftTwo.card = 2 →
      IsCupSet χ (leftTwo ∪ two)) :
    IsCupSet χ (three ∪ two) := by
  classical
  intro t hi hj hk
  by_cases hallThree : t.i ∈ three ∧ t.j ∈ three ∧ t.k ∈ three
  · exact hthreeCup t hallThree.1 hallThree.2.1 hallThree.2.2
  let tripleSet : Finset (Fin n) := {t.i, t.j, t.k}
  have htripleCard : tripleSet.card = 3 := by
    simp [tripleSet, ne_of_lt t.hij, ne_of_lt t.hjk,
      ne_of_lt (t.hij.trans t.hjk)]
  have hinterCard : (tripleSet ∩ three).card ≤ 2 := by
    by_contra hnot
    have hinterSub : tripleSet ∩ three ⊆ tripleSet := Finset.inter_subset_left
    have hinterEq : tripleSet ∩ three = tripleSet := by
      apply (Finset.subset_iff_eq_of_card_le ?_).mp hinterSub
      rw [htripleCard]
      omega
    apply hallThree
    constructor
    · have : t.i ∈ tripleSet ∩ three := by
        rw [hinterEq]
        simp [tripleSet]
      exact (Finset.mem_inter.mp this).2
    constructor
    · have : t.j ∈ tripleSet ∩ three := by
        rw [hinterEq]
        simp [tripleSet]
      exact (Finset.mem_inter.mp this).2
    · have : t.k ∈ tripleSet ∩ three := by
        rw [hinterEq]
        simp [tripleSet]
      exact (Finset.mem_inter.mp this).2
  obtain ⟨leftTwo, hinterSubLeftTwo, hleftTwoSub, hleftTwoCard⟩ :=
    Finset.exists_subsuperset_card_eq Finset.inter_subset_right
      hinterCard (show 2 ≤ three.card by omega)
  have htwoTwoCup := hallTwoTwo leftTwo hleftTwoSub hleftTwoCard
  apply htwoTwoCup t
  · rcases Finset.mem_union.mp hi with hiThree | hiTwo
    · exact Finset.mem_union_left _ (hinterSubLeftTwo
        (Finset.mem_inter.mpr ⟨by simp [tripleSet], hiThree⟩))
    · exact Finset.mem_union_right _ hiTwo
  · rcases Finset.mem_union.mp hj with hjThree | hjTwo
    · exact Finset.mem_union_left _ (hinterSubLeftTwo
        (Finset.mem_inter.mpr ⟨by simp [tripleSet], hjThree⟩))
    · exact Finset.mem_union_right _ hjTwo
  · rcases Finset.mem_union.mp hk with hkThree | hkTwo
    · exact Finset.mem_union_left _ (hinterSubLeftTwo
        (Finset.mem_inter.mpr ⟨by simp [tripleSet], hkThree⟩))
    · exact Finset.mem_union_right _ hkTwo

/-- The complete extreme `7+1` root profile.  Splitting the lower vertices at
the unique upper vertex either exposes five vertices on one side (which the
upper endpoint extends), or leaves at least two on both sides.  In the latter
case a non-cup balanced four-set directly defeats density, while universal
balanced four-cups glue any internal three-cup to a five-cup and force a
five-set with no four-cup. -/
theorem deepSplit_lowerSeven_upperOne_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 7) (hupperCard : upper.card = 1)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  classical
  obtain ⟨q, hupperEq⟩ := Finset.card_eq_one.mp hupperCard
  subst upper
  have hqUpper : q ∈ ({q} : Finset (Fin n)) := by simp
  have hqNotLower : q ∉ lower := fun hqLower =>
    (Finset.disjoint_left.mp hdeep.disjoint) hqLower hqUpper
  let below := lower.filter (fun x => x < q)
  let above := lower.filter (fun x => q < x)
  have hbelowSub : below ⊆ lower := by
    exact Finset.filter_subset _ _
  have haboveSub : above ⊆ lower := by
    exact Finset.filter_subset _ _
  have hbelowLt {x : Fin n} (hx : x ∈ below) : x < q := by
    exact (Finset.mem_filter.mp hx).2
  have haboveGt {x : Fin n} (hx : x ∈ above) : q < x := by
    exact (Finset.mem_filter.mp hx).2
  have hbelowAbove : Disjoint below above := by
    apply Finset.disjoint_left.mpr
    intro x hxBelow hxAbove
    exact (not_lt_of_ge (le_of_lt (hbelowLt hxBelow))) (haboveGt hxAbove)
  have hbelowUnionAbove : below ∪ above = lower := by
    ext x
    simp only [Finset.mem_union, below, above, Finset.mem_filter]
    constructor
    · rintro (⟨hxLower, _⟩ | ⟨hxLower, _⟩) <;> exact hxLower
    · intro hxLower
      have hxNe : x ≠ q := fun hxq => hqNotLower (hxq ▸ hxLower)
      rcases lt_or_gt_of_ne hxNe with hxq | hqx
      · exact Or.inl ⟨hxLower, hxq⟩
      · exact Or.inr ⟨hxLower, hqx⟩
  have hsideCards : below.card + above.card = 7 := by
    rw [← Finset.card_union_of_disjoint hbelowAbove, hbelowUnionAbove,
      hlowerCard]
  by_cases hbelowSmall : below.card ≤ 1
  · have haboveFive : 5 ≤ above.card := by omega
    obtain ⟨five, hfiveSubAbove, hfiveCard⟩ :=
      Finset.exists_subset_card_eq haboveFive
    obtain ⟨cup, hcupMem, hcupSubFive⟩ := hdense five
      (hfiveSubAbove.trans haboveSub |>.trans Finset.subset_union_left)
      hfiveCard
    have hcupData := mem_capWitnesses.mp hcupMem
    have hcupSubLower : cup ⊆ lower :=
      hcupSubFive.trans hfiveSubAbove |>.trans haboveSub
    have hqLeft : HasDeepBelowSplit.IsLeftSweepEndpoint cup q := by
      intro x hxCup
      exact le_of_lt (haboveGt (hfiveSubAbove (hcupSubFive hxCup)))
    exact hdeep.containsCupSet_succ_of_upper_endpoint hcupSubLower
      hcupData.2.1 (isCapSet_dual_iff.mp hcupData.2.2) hqUpper (Or.inl hqLeft)
  by_cases haboveSmall : above.card ≤ 1
  · have hbelowFive : 5 ≤ below.card := by omega
    obtain ⟨five, hfiveSubBelow, hfiveCard⟩ :=
      Finset.exists_subset_card_eq hbelowFive
    obtain ⟨cup, hcupMem, hcupSubFive⟩ := hdense five
      (hfiveSubBelow.trans hbelowSub |>.trans Finset.subset_union_left)
      hfiveCard
    have hcupData := mem_capWitnesses.mp hcupMem
    have hcupSubLower : cup ⊆ lower :=
      hcupSubFive.trans hfiveSubBelow |>.trans hbelowSub
    have hqRight : HasDeepBelowSplit.IsRightSweepEndpoint cup q := by
      intro x hxCup
      exact le_of_lt (hbelowLt (hfiveSubBelow (hcupSubFive hxCup)))
    exact hdeep.containsCupSet_succ_of_upper_endpoint hcupSubLower
      hcupData.2.1 (isCapSet_dual_iff.mp hcupData.2.2) hqUpper (Or.inr hqRight)
  have hbelowTwo : 2 ≤ below.card := by omega
  have haboveTwo : 2 ≤ above.card := by omega
  by_contra hnoCupFive
  by_cases hbalanced : ∀ belowTwo aboveTwo : Finset (Fin n),
      belowTwo ⊆ below → belowTwo.card = 2 →
      aboveTwo ⊆ above → aboveTwo.card = 2 →
      IsCupSet χ (belowTwo ∪ aboveTwo)
  · have hbalancedImpossible
        (big small : Finset (Fin n))
        (hbigSub : big ⊆ lower) (hsmallSub : small ⊆ lower)
        (hbigSmall : Disjoint big small)
        (hbigFour : 4 ≤ big.card) (hsmallTwo : 2 ≤ small.card)
        (hall : ∀ bigTwo smallTwo : Finset (Fin n),
          bigTwo ⊆ big → bigTwo.card = 2 →
          smallTwo ⊆ small → smallTwo.card = 2 →
          IsCupSet χ (bigTwo ∪ smallTwo)) : False := by
      obtain ⟨bigFour, hbigFourSub, hbigFourCard⟩ :=
        Finset.exists_subset_card_eq hbigFour
      obtain ⟨smallTwo, hsmallTwoSub, hsmallTwoCard⟩ :=
        Finset.exists_subset_card_eq hsmallTwo
      have hbigFourSmallTwo : Disjoint bigFour smallTwo :=
        hbigSmall.mono hbigFourSub hsmallTwoSub
      have hbigTripleNotCup (three : Finset (Fin n))
          (hthreeSub : three ⊆ bigFour) (hthreeCard : three.card = 3) :
          ¬IsCupSet χ three := by
        intro hthreeCup
        have hglued : IsCupSet χ (three ∪ smallTwo) :=
          isCupSet_union_three_two_of_all_two_two hthreeCard hthreeCup
            (fun leftTwo hleftSub hleftCard =>
              hall leftTwo smallTwo (hleftSub.trans hthreeSub |>.trans hbigFourSub)
                hleftCard hsmallTwoSub hsmallTwoCard)
        have hgluedCard : (three ∪ smallTwo).card = 5 := by
          rw [Finset.card_union_of_disjoint
            (hbigFourSmallTwo.mono hthreeSub (show smallTwo ⊆ smallTwo from fun _ h => h)),
            hthreeCard, hsmallTwoCard]
        have hgluedSub : three ∪ smallTwo ⊆ lower :=
          Finset.union_subset
            (hthreeSub.trans hbigFourSub |>.trans hbigSub)
            (hsmallTwoSub.trans hsmallSub)
        exact hnoCupFive ⟨three ∪ smallTwo,
          hgluedSub.trans Finset.subset_union_left, hgluedCard, hglued⟩
      obtain ⟨s, hsSmallTwo⟩ := Finset.card_pos.mp (by omega : 0 < smallTwo.card)
      have hsNotBigFour : s ∉ bigFour := fun hsBig =>
        (Finset.disjoint_left.mp hbigFourSmallTwo) hsBig hsSmallTwo
      let five := insert s bigFour
      have hfiveCard : five.card = 5 := by
        simp [five, Finset.card_insert_of_notMem hsNotBigFour, hbigFourCard]
      have hfiveSub : five ⊆ lower ∪ {q} := by
        exact Finset.insert_subset
          (Finset.mem_union_left _ (hsmallSub (hsmallTwoSub hsSmallTwo)))
          (hbigFourSub.trans hbigSub |>.trans Finset.subset_union_left)
      obtain ⟨cup, hcupMem, hcupSubFive⟩ := hdense five hfiveSub hfiveCard
      have hcupData := mem_capWitnesses.mp hcupMem
      have hcupSet : IsCupSet χ cup := isCapSet_dual_iff.mp hcupData.2.2
      by_cases hsCup : s ∈ cup
      · let three := cup.erase s
        have hthreeCard : three.card = 3 := by
          simp [three, Finset.card_erase_of_mem hsCup, hcupData.2.1]
        have hthreeSub : three ⊆ bigFour := by
          intro y hyThree
          have hyCup := (Finset.mem_erase.mp hyThree).2
          have hyNe := (Finset.mem_erase.mp hyThree).1
          rcases Finset.mem_insert.mp (hcupSubFive hyCup) with hys | hyBig
          · exact (hyNe hys).elim
          · exact hyBig
        exact hbigTripleNotCup three hthreeSub hthreeCard
          (FinsetPolygon.IsCupSet.mono hcupSet (Finset.erase_subset s cup))
      · have hcupSubBig : cup ⊆ bigFour := by
          intro y hyCup
          rcases Finset.mem_insert.mp (hcupSubFive hyCup) with hys | hyBig
          · exact (hsCup (hys ▸ hyCup)).elim
          · exact hyBig
        have hcupEqBig : cup = bigFour := by
          apply (Finset.subset_iff_eq_of_card_le ?_).mp hcupSubBig
          rw [hbigFourCard, hcupData.2.1]
        have hbigFourCup : IsCupSet χ bigFour := hcupEqBig ▸ hcupSet
        have hthreeLe : 3 ≤ bigFour.card := by omega
        obtain ⟨three, hthreeSub, hthreeCard⟩ :=
          Finset.exists_subset_card_eq hthreeLe
        exact hbigTripleNotCup three hthreeSub hthreeCard
          (FinsetPolygon.IsCupSet.mono hbigFourCup hthreeSub)
    have hlarge : 4 ≤ below.card ∨ 4 ≤ above.card := by omega
    rcases hlarge with hbelowFour | haboveFour
    · exact hbalancedImpossible below above hbelowSub haboveSub
        hbelowAbove hbelowFour haboveTwo
        (fun bigTwo smallTwo hbigSub hbigCard hsmallSub hsmallCard =>
          hbalanced bigTwo smallTwo hbigSub hbigCard hsmallSub hsmallCard)
    · exact hbalancedImpossible above below haboveSub hbelowSub
        hbelowAbove.symm haboveFour hbelowTwo
        (fun bigTwo smallTwo hbigSub hbigCard hsmallSub hsmallCard => by
          simpa [Finset.union_comm] using
            hbalanced smallTwo bigTwo hsmallSub hsmallCard hbigSub hbigCard)
  · push Not at hbalanced
    obtain ⟨belowTwo, aboveTwo, hbelowTwoSub, hbelowTwoCard,
      haboveTwoSub, haboveTwoCard, hfourNotCup⟩ := hbalanced
    have htwoTwoDisjoint : Disjoint belowTwo aboveTwo :=
      hbelowAbove.mono hbelowTwoSub haboveTwoSub
    let four := belowTwo ∪ aboveTwo
    have hfourCard : four.card = 4 := by
      change (belowTwo ∪ aboveTwo).card = 4
      rw [Finset.card_union_of_disjoint htwoTwoDisjoint,
        hbelowTwoCard, haboveTwoCard]
    have hfourSubLower : four ⊆ lower :=
      Finset.union_subset (hbelowTwoSub.trans hbelowSub)
        (haboveTwoSub.trans haboveSub)
    have hqNotFour : q ∉ four := fun hqFour =>
      hqNotLower (hfourSubLower hqFour)
    let five := insert q four
    have hfiveCard : five.card = 5 := by
      simp [five, Finset.card_insert_of_notMem hqNotFour, hfourCard]
    have hfiveSub : five ⊆ lower ∪ {q} :=
      Finset.insert_subset (Finset.mem_union_right _ hqUpper)
        (hfourSubLower.trans Finset.subset_union_left)
    obtain ⟨cup, hcupMem, hcupSubFive⟩ := hdense five hfiveSub hfiveCard
    have hcupData := mem_capWitnesses.mp hcupMem
    have hcupSet : IsCupSet χ cup := isCapSet_dual_iff.mp hcupData.2.2
    have hqCup : q ∈ cup := by
      by_contra hqNotCup
      have hcupSubFour : cup ⊆ four := by
        intro y hyCup
        rcases Finset.mem_insert.mp (hcupSubFive hyCup) with hyq | hyFour
        · exact (hqNotCup (hyq ▸ hyCup)).elim
        · exact hyFour
      have hcupEqFour : cup = four := by
        apply (Finset.subset_iff_eq_of_card_le ?_).mp hcupSubFour
        rw [hfourCard, hcupData.2.1]
      have hfourCup : IsCupSet χ four := hcupEqFour ▸ hcupSet
      exact hfourNotCup (by simpa [four] using hfourCup)
    have hcupLower : (cup ∩ lower).Nonempty := by
      apply Finset.card_pos.mp
      have hpartition := card_eq_lowerInter_add_upperInter_of_subset_union
        hdeep.disjoint hcupData.1
      have hupperLe := Finset.card_le_card
        (show cup ∩ ({q} : Finset (Fin n)) ⊆ {q} from Finset.inter_subset_right)
      rw [hcupData.2.1] at hpartition
      simp only [Finset.card_singleton] at hupperLe
      omega
    have hbelowCup : (cup ∩ below).Nonempty := by
      by_contra hempty
      have heraseSub : cup.erase q ⊆ aboveTwo := by
        intro y hyErase
        have hyCup := (Finset.mem_erase.mp hyErase).2
        have hyNe := (Finset.mem_erase.mp hyErase).1
        rcases Finset.mem_insert.mp (hcupSubFive hyCup) with hyq | hyFour
        · exact (hyNe hyq).elim
        rcases Finset.mem_union.mp hyFour with hyBelow | hyAbove
        · have : y ∈ cup ∩ below := Finset.mem_inter.mpr
            ⟨hyCup, hbelowTwoSub hyBelow⟩
          exact (hempty ⟨y, this⟩).elim
        · exact hyAbove
      have hle := Finset.card_le_card heraseSub
      rw [Finset.card_erase_of_mem hqCup, hcupData.2.1,
        haboveTwoCard] at hle
      omega
    have haboveCup : (cup ∩ above).Nonempty := by
      by_contra hempty
      have heraseSub : cup.erase q ⊆ belowTwo := by
        intro y hyErase
        have hyCup := (Finset.mem_erase.mp hyErase).2
        have hyNe := (Finset.mem_erase.mp hyErase).1
        rcases Finset.mem_insert.mp (hcupSubFive hyCup) with hyq | hyFour
        · exact (hyNe hyq).elim
        rcases Finset.mem_union.mp hyFour with hyBelow | hyAbove
        · exact hyBelow
        · have : y ∈ cup ∩ above := Finset.mem_inter.mpr
            ⟨hyCup, haboveTwoSub hyAbove⟩
          exact (hempty ⟨y, this⟩).elim
      have hle := Finset.card_le_card heraseSub
      rw [Finset.card_erase_of_mem hqCup, hcupData.2.1,
        hbelowTwoCard] at hle
      omega
    obtain ⟨b, hbInter⟩ := hbelowCup
    have hbCup := (Finset.mem_inter.mp hbInter).1
    have hbBelow := (Finset.mem_inter.mp hbInter).2
    obtain ⟨a, haInter⟩ := haboveCup
    have haCup := (Finset.mem_inter.mp haInter).1
    have haAbove := (Finset.mem_inter.mp haInter).2
    have hendpoint := hdeep.upper_mem_cup_isSweepEndpoint
      hcupData.1 hcupSet hcupLower hqCup hqUpper
    have hnotEndpoint : ¬HasDeepBelowSplit.IsSweepEndpoint cup q := by
      rw [HasDeepBelowSplit.not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
      exact ⟨⟨b, hbCup, hbelowLt hbBelow⟩,
        ⟨a, haCup, haboveGt haAbove⟩⟩
    exact hnotEndpoint hendpoint

/-! ## Assembly and the local transversal consumer -/

/-- Root-only form of the eight-vertex obstruction.  Recursive
decomposability is not used after exposing one genuine nonempty root split. -/
theorem eightVertex_deepSplit_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlowerNonempty : lower.Nonempty) (hupperNonempty : upper.Nonempty)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcard : (lower ∪ upper).card = 8)
    (hdense : HasFourCupInEveryFiveSubset578 χ (lower ∪ upper)) :
    ContainsCupSet χ (lower ∪ upper) 5 := by
  have hsum : lower.card + upper.card = 8 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint, hcard]
  have hlowerPos : 0 < lower.card := Finset.card_pos.mpr hlowerNonempty
  have hupperPos : 0 < upper.card := Finset.card_pos.mpr hupperNonempty
  by_cases hsmall : lower.card ≤ 3
  · exact deepSplit_smallLower_denseFourCups_force_cupFive hdeep hcard
      hlowerNonempty hsmall hdense
  by_cases hfour : lower.card = 4
  · exact deepSplit_lowerFour_upperFour_denseFourCups_force_cupFive hdeep
      hfour (by omega) hdense
  by_cases hfive : lower.card = 5
  · exact deepSplit_lowerFive_upperThree_denseFourCups_force_cupFive hdeep
      hfive (by omega) hdense
  by_cases hsix : lower.card = 6
  · exact deepSplit_lowerSix_upperTwo_denseFourCups_force_cupFive hdeep
      hsix (by omega) hdense
  · exact deepSplit_lowerSeven_upperOne_denseFourCups_force_cupFive hdeep
      (by omega) (by omega) hdense

/-- The reviewed eight-vertex theorem in its originally selected form. -/
theorem eightVertex_decomposable_denseFourCups_force_cupFive
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hdecomp : IsDecomposableOn χ carrier)
    (hcard : carrier.card = 8)
    (hdense : HasFourCupInEveryFiveSubset578 χ carrier) :
    ContainsCupSet χ carrier 5 := by
  obtain ⟨lower, upper, hlowerNonempty, hupperNonempty, _, _, hdeep, hsplit⟩ :=
    hdecomp.exists_split (by omega)
  subst carrier
  exact eightVertex_deepSplit_denseFourCups_force_cupFive
    hlowerNonempty hupperNonempty hdeep hcard hdense

/-- Every decomposable carrier of exactly eight vertices either already has a
five-cup or admits a three-vertex transversal of all its four-cups. -/
theorem eightVertex_decomposable_fourCupFamily_has_threeTransversal_or_cupFive
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hdecomp : IsDecomposableOn χ carrier)
    (hcard : carrier.card = 8) :
    ContainsCupSet χ carrier 5 ∨
      ∃ boundary : Finset (Fin n),
        boundary ⊆ carrier ∧ boundary.card ≤ 3 ∧
          IsCupWitnessTransversal578 χ carrier boundary 4 := by
  classical
  by_cases hcupFive : ContainsCupSet χ carrier 5
  · exact Or.inl hcupFive
  · right
    by_contra hnoBoundary
    have hdense := hasFourCupInEveryFiveSubset_of_no_threeTransversal
      hcard hnoBoundary
    exact hcupFive
      (eightVertex_decomposable_denseFourCups_force_cupFive
        hdecomp hcard hdense)

/-- The exact eight-vertex result and the previous at-most-seven theorem give
the uniform local consumer needed at a small decomposition child. -/
theorem atMostEight_decomposable_fourCupFamily_has_threeTransversal_or_cupFive
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hdecomp : IsDecomposableOn χ carrier)
    (hcard : carrier.card ≤ 8) :
    ContainsCupSet χ carrier 5 ∨
      ∃ boundary : Finset (Fin n),
        boundary ⊆ carrier ∧ boundary.card ≤ 3 ∧
          IsCupWitnessTransversal578 χ carrier boundary 4 := by
  by_cases height : carrier.card = 8
  · exact eightVertex_decomposable_fourCupFamily_has_threeTransversal_or_cupFive
      hdecomp height
  · exact atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive (by omega)

/-- Exact state-578 consumer for any eight-vertex remainder of a decomposable
reservoir: global five-cup avoidance turns the local dichotomy into a genuine
three-vertex four-cup boundary. -/
theorem exists_threeTransversal_on_decomposable_eightSubset_of_no_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {reservoir carrier : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcarrierSub : carrier ⊆ reservoir) (hcard : carrier.card = 8)
    (hnoCup : ¬ContainsCupSet χ reservoir 5) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ carrier ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ carrier boundary 4 := by
  have hcarrierNonempty : carrier.Nonempty :=
    Finset.card_pos.mp (show 0 < carrier.card by omega)
  have hcarrierDecomp := hreservoir.subset hcarrierSub hcarrierNonempty
  rcases eightVertex_decomposable_fourCupFamily_has_threeTransversal_or_cupFive
      hcarrierDecomp hcard with hcupFive | hboundary
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive hcarrierSub)).elim
  · exact hboundary

/-- The eight unused vertices outside the six-cap saturation carry a
three-boundary under the live no-five-cup hypothesis. -/
theorem SixCapSaturation578.unusedSupport_exists_threeTransversal
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hsupport : IsDecomposableOn χ support) (hcard : support.card = 32)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ support \ saturation.capSupport ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (support \ saturation.capSupport) boundary 4 := by
  exact exists_threeTransversal_on_decomposable_eightSubset_of_no_cupFive
    hsupport Finset.sdiff_subset (saturation.unusedSupport_card_at_32 hcard)
    hnoCup

/-- The same boundary is available on the eight vertices unused by the
original disjoint three-cup/three-cap packing. -/
theorem ThreeDisjointCupCapFourPacking578.unusedSupport_exists_threeTransversal
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (hsupport : IsDecomposableOn χ support) (hcard : support.card = 32)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ support \ packing.selectedSupport ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (support \ packing.selectedSupport) boundary 4 := by
  exact exists_threeTransversal_on_decomposable_eightSubset_of_no_cupFive
    hsupport Finset.sdiff_subset (packing.unusedSupport_card_at_32 hcard)
    hnoCup

/-- The protected one-cup/five-cap packing has the same exact `24+8`
boundary consequence. -/
theorem ProtectedCupFiveCapPacking578.unusedSupport_exists_threeTransversal
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ProtectedCupFiveCapPacking578 χ support)
    (hsupport : IsDecomposableOn χ support) (hcard : support.card = 32)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ support \ packing.selectedSupport ∧ boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (support \ packing.selectedSupport) boundary 4 := by
  exact exists_threeTransversal_on_decomposable_eightSubset_of_no_cupFive
    hsupport Finset.sdiff_subset (packing.unusedSupport_card_at_32 hcard)
    hnoCup

/-- In the tight one-spine branch, the new unused three-boundary does not
magically hit the full residual family.  Instead density produces the exact
next witness: a residual cup disjoint from that boundary which necessarily
crosses from the unused eight vertices into the selected six-cap support.
Because the full address matrix indexes every residual cup, this witness is a
genuine new matrix row rather than an incidence-only proposal. -/
theorem PrivateCupStarSixCapState578.exists_unusedBoundary_and_crossingResidualCup_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    ∃ boundary : Finset (Fin n),
      boundary ⊆ reservoir \ joint.saturation.capSupport ∧
      boundary.card ≤ 3 ∧
      IsCupWitnessTransversal578 χ
        (reservoir \ joint.saturation.capSupport) boundary 4 ∧
      ∃ cup,
        cup ∈ joint.ledger.residualCupFamily
          (joint.saturation.state.packing.fullCupProtected
            joint.ledger.transversal) ∧
        Disjoint cup boundary ∧
        ¬cup ⊆ reservoir \ joint.saturation.capSupport ∧
        (cup ∩ joint.saturation.capSupport).Nonempty := by
  obtain ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits⟩ :=
    joint.saturation.unusedSupport_exists_threeTransversal
      hreservoir hcard hnoCup
  have hlocalHits : ∀ cup,
      cup ∈ capWitnesses χ.dual reservoir 4 →
      cup ⊆ reservoir \ joint.saturation.capSupport →
      ¬Disjoint cup boundary := by
    intro cup hcup hcupSub
    have hcupData := mem_capWitnesses.mp hcup
    exact hboundaryHits.2 cup
      (mem_capWitnesses.mpr ⟨hcupSub, hcupData.2⟩)
  obtain ⟨cup, hcupResidual, hcupBoundary, hcupNotUnused⟩ :=
    exists_escapingResidualCup578_of_localBoundary joint
      hreservoir hcard hnoCap hnoStrong hone Finset.sdiff_subset
      hboundarySub hboundaryCard hlocalHits
  have hcupAmbient :=
    (joint.ledger.mem_residualCupFamily.mp hcupResidual).1
  have hcrosses : (cup ∩ joint.saturation.capSupport).Nonempty := by
    obtain ⟨x, hxCup, hxNotUnused⟩ := Finset.not_subset.mp hcupNotUnused
    have hxCapSupport : x ∈ joint.saturation.capSupport := by
      by_contra hxNotCapSupport
      exact hxNotUnused (Finset.mem_sdiff.mpr
        ⟨(mem_capWitnesses.mp hcupAmbient).1 hxCup, hxNotCapSupport⟩)
    exact ⟨x, Finset.mem_inter.mpr ⟨hxCup, hxCapSupport⟩⟩
  exact ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits,
    cup, hcupResidual, hcupBoundary, hcupNotUnused, hcrosses⟩

end ErdosSzekeres
