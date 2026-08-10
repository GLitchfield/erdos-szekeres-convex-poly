module

public import ErdosSzekeres.StructuralChargingNextState578ExteriorDensity

@[expose] public section

/-!
# Full blocker-avoiding density at state `(5,7,8)`

The exterior-density theorem selects five deletion entries avoiding one of six
saturated cap columns.  This file retains the missing information needed to
compare those entries with every ambient four-cup avoiding the same blocker.

The new matrix is deliberately infrastructure rather than a terminal claim.
Its rows are the complete blocker-avoiding cup family, not only the residual
family filtered by the private-cup transversal.  The exact relation between
the two matrices remains an open synchronization problem.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-! ## Retaining the all-base/source-meeting fan data -/

/-- The positive deletion-fan branch together with the two hypotheses used to
construct it.  The earlier total reconnect made their failures explicit but
discarded their proofs in the positive branch.  Retaining them is essential:
it certifies that every indexed source actually belongs to its deletion cup. -/
structure AllBaseMeetingNineOneSidedDeletionFan578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty) where
  fan : NineOneSidedDeletionFan578 ledger minimum hupper
  all_base : ∀ j c, (matrix.cell (ledger.cupAt j c) j).path =
    (matrix.cell minimum.row minimum.column).path
  all_meet : ∀ j c, ¬Disjoint (ledger.cupAt j c).1
    (joint.saturation.capAt j)

theorem AllBaseMeetingNineOneSidedDeletionFan578.source_mem_row
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j}) :
    c.1 ∈ (ledger.cupAt j c).1 :=
  ledger.source_mem_of_not_disjoint j c (witness.all_meet j c)

/-- The source projection is injective on the fan entry set because distinct
cap columns are disjoint. -/
theorem NineOneSidedDeletionFan578.entry_source_injective
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper) :
    Function.Injective (fun p : {p // p ∈ fan.entries} ↦ p.1.2.1) := by
  rintro ⟨⟨pj, pc⟩, hp⟩ ⟨⟨rj, rc⟩, hr⟩ heq
  simp only at heq ⊢
  have hcolumn : pj = rj := by
    by_contra hne
    have hdisjoint := joint.saturation.capAt_disjoint_of_ne hne
    exact (Finset.disjoint_left.mp hdisjoint) pc.2
      (by rw [heq]; exact rc.2)
  subst rj
  have hsource : pc = rc := Subtype.ext heq
  subst rc
  rfl

/-- Entries of one all-base meeting fan which select the same deletion cup. -/
def NineOneSidedDeletionFan578.cupFiberEntries
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (cup : Finset (Fin n)) :
    Finset (Σ j : Fin 6,
      {c : Fin n // c ∈ joint.saturation.capAt j}) :=
  fan.entries.filter fun p ↦ (ledger.cupAt p.1 p.2).1 = cup

/-- A one-upper deletion cup can carry at most three distinct fan sources.
This is the first multiplicity statement which needs the retained `all_meet`
proof: it maps every entry in a repeated-cup fiber injectively into the cup's
three lower vertices. -/
theorem AllBaseMeetingNineOneSidedDeletionFan578.cupFiberEntries_card_le_three
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (cup : Finset (Fin n)) :
    (witness.fan.cupFiberEntries cup).card ≤ 3 := by
  classical
  let fiber := witness.fan.cupFiberEntries cup
  by_cases hempty : fiber = ∅
  · simp [fiber, hempty]
  · have hnonempty : fiber.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨p, hpFiber⟩ := hnonempty
    have hpEntry : p ∈ witness.fan.entries :=
      (Finset.mem_filter.mp hpFiber).1
    have hpSource : p.2.1 ∈ witness.fan.sources :=
      (Finset.mem_filter.mp hpEntry).2
    have hpCup : (ledger.cupAt p.1 p.2).1 = cup :=
      (Finset.mem_filter.mp hpFiber).2
    have hshape : CupFourOneUpperEndpointShape578 cup
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper := by
      rw [← hpCup]
      exact witness.fan.row_oneUpper p.1 p.2 hpSource
    have hinterCard :
        (cup ∩ (matrix.cell minimum.row minimum.column).node.lower).card ≤ 3 :=
      hshape.inter_lower_card_le_three
        (matrix.cell minimum.row minimum.column).node.deep.disjoint
    let source (r : {r // r ∈ fiber}) :
        {x // x ∈ cup ∩
          (matrix.cell minimum.row minimum.column).node.lower} := by
      have hrData := Finset.mem_filter.mp r.2
      have hrCup : (ledger.cupAt r.1.1 r.1.2).1 = cup := hrData.2
      refine ⟨r.1.2.1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [← hrCup]
        exact witness.source_mem_row r.1.1 r.1.2
      · exact hcaps (joint.saturation.capAt_subset_capSupport r.1.1 r.1.2.2)
    have hinjective : Function.Injective source := by
      intro r s hrs
      have hsource : r.1.2.1 = s.1.2.1 := congrArg Subtype.val hrs
      let rEntry : {p // p ∈ witness.fan.entries} :=
        ⟨r.1, (Finset.mem_filter.mp r.2).1⟩
      let sEntry : {p // p ∈ witness.fan.entries} :=
        ⟨s.1, (Finset.mem_filter.mp s.2).1⟩
      have hentry : rEntry = sEntry :=
        witness.fan.entry_source_injective hsource
      apply Subtype.ext
      change r.1 = s.1
      exact congrArg
        (fun e : {p // p ∈ witness.fan.entries} ↦ e.1) hentry
    have hcard := Fintype.card_le_of_injective source hinjective
    have hinterFintype :
        Fintype.card {x // x ∈ cup ∩
          (matrix.cell minimum.row minimum.column).node.lower} ≤ 3 := by
      simpa only [Fintype.card_coe] using hinterCard
    simpa only [Fintype.card_coe] using hcard.trans hinterFintype

/-- Fan entries whose selected deletion cup avoids one fixed cap column. -/
def NineOneSidedDeletionFan578.deficitEntriesAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (blocker : Fin 6) :
    Finset (Σ j : Fin 6,
      {c : Fin n // c ∈ joint.saturation.capAt j}) :=
  fan.entries.filter fun p ↦
    Disjoint (ledger.cupAt p.1 p.2).1
      (joint.saturation.capAt blocker)

/-- The distinct deletion cups represented by one deficit column. -/
def NineOneSidedDeletionFan578.deficitCupsAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (blocker : Fin 6) : Finset (Finset (Fin n)) :=
  (fan.deficitEntriesAt blocker).image fun p ↦
    (ledger.cupAt p.1 p.2).1

/-- Five deficit entries represent at least two genuinely distinct cups.  The
factor three is sharp at the level of the retained one-upper/source data. -/
theorem AllBaseMeetingNineOneSidedDeletionFan578.two_le_deficitCupsAt_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (blocker : Fin 6)
    (hfive : 5 ≤ (witness.fan.deficitEntriesAt blocker).card) :
    2 ≤ (witness.fan.deficitCupsAt blocker).card := by
  classical
  let entries := witness.fan.deficitEntriesAt blocker
  let cups := witness.fan.deficitCupsAt blocker
  let cupAtEntry := fun p :
      Σ j : Fin 6, {c : Fin n // c ∈ joint.saturation.capAt j} ↦
    (ledger.cupAt p.1 p.2).1
  have hmaps : ∀ p ∈ entries, cupAtEntry p ∈ cups := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfiber (cup : Finset (Fin n)) :
      (entries.filter fun p ↦ cupAtEntry p = cup).card ≤ 3 := by
    have hsub : (entries.filter fun p ↦ cupAtEntry p = cup) ⊆
        witness.fan.cupFiberEntries cup := by
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hpData.1).1, hpData.2⟩
    exact (Finset.card_le_card hsub).trans
      (witness.cupFiberEntries_card_le_three hcaps cup)
  have hdecomp : entries.card =
      ∑ cup ∈ cups, (entries.filter fun p ↦ cupAtEntry p = cup).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : entries.card ≤ 3 * cups.card := by
    rw [hdecomp]
    calc
      (∑ cup ∈ cups,
          (entries.filter fun p ↦ cupAtEntry p = cup).card) ≤
          ∑ _cup ∈ cups, 3 := Finset.sum_le_sum fun cup _ ↦ hfiber cup
      _ = 3 * cups.card := by simp [Nat.mul_comm]
  change 5 ≤ entries.card at hfive
  change 2 ≤ cups.card
  omega

/-- The six-column deficit theorem and the multiplicity-three bound together
produce a column avoided by at least two distinct deletion cups. -/
theorem AllBaseMeetingNineOneSidedDeletionFan578.exists_twoDistinctDeficitCups
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∃ blocker : Fin 6,
      2 ≤ (witness.fan.deficitCupsAt blocker).card := by
  obtain ⟨blocker, hfive⟩ := witness.fan.exists_fiveDeficitColumn hcaps
  exact ⟨blocker, witness.two_le_deficitCupsAt_card hcaps blocker hfive⟩

/-! ## The full blocker-avoiding cup family -/

/-- Every ambient four-cup disjoint from one selected saturated cap. -/
def BlockerAvoidingCupIndex578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) (blocker : Fin 6) :=
  {cup : Finset (Fin n) //
    cup ∈ capWitnesses χ.dual support 4 ∧
      Disjoint cup (joint.saturation.capAt blocker)}

theorem BlockerAvoidingCupIndex578.mem_cupWitnesses
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support} {blocker : Fin 6}
    (cup : BlockerAvoidingCupIndex578 joint blocker) :
    cup.1 ∈ capWitnesses χ.dual support 4 :=
  cup.2.1

theorem BlockerAvoidingCupIndex578.disjoint_blocker
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support} {blocker : Fin 6}
    (cup : BlockerAvoidingCupIndex578 joint blocker) :
    Disjoint cup.1 (joint.saturation.capAt blocker) :=
  cup.2.2

/-- Every residual-family row which avoids a selected cap is also a row of
the complete blocker-avoiding family. -/
def PrivateCupStarSixCapState578.ResidualCupIndex.toBlockerAvoiding
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support} {blocker : Fin 6}
    (cup : joint.ResidualCupIndex)
    (hdisjoint : Disjoint cup.1 (joint.saturation.capAt blocker)) :
    BlockerAvoidingCupIndex578 joint blocker :=
  ⟨cup.1, (joint.ledger.mem_residualCupFamily.mp cup.2).1, hdisjoint⟩

/-- Every distinct deletion cup counted in a deficit column is represented
in the complete blocker-avoiding family.  This is the exact selected-row to
full-family synchronization supplied by incidence alone. -/
theorem AllBaseMeetingNineOneSidedDeletionFan578.deficitCup_has_blockerAvoidingIndex
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper)
    (blocker : Fin 6) {cup : Finset (Fin n)}
    (hcup : cup ∈ witness.fan.deficitCupsAt blocker) :
    ∃ indexed : BlockerAvoidingCupIndex578 joint blocker,
      indexed.1 = cup := by
  classical
  obtain ⟨p, hpDeficit, hpCup⟩ := Finset.mem_image.mp hcup
  have hpDisjoint : Disjoint (ledger.cupAt p.1 p.2).1
      (joint.saturation.capAt blocker) :=
    (Finset.mem_filter.mp hpDeficit).2
  exact ⟨(ledger.cupAt p.1 p.2).toBlockerAvoiding hpDisjoint, hpCup⟩

/-- Package an arbitrary four-cup and a proof that it avoids the blocker. -/
def FourCupIndex578.toBlockerAvoiding
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support} {blocker : Fin 6}
    (cup : FourCupIndex578 χ support)
    (hdisjoint : Disjoint cup.1 (joint.saturation.capAt blocker)) :
    BlockerAvoidingCupIndex578 joint blocker :=
  ⟨cup.1, cup.2, hdisjoint⟩

/-! ## The blocker-avoiding cup/six-cap matrix -/

/-- Pair every blocker-avoiding cup with all six saturated caps. -/
structure BlockerAvoidingCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) (blocker : Fin 6) where
  cell : ∀ cup : BlockerAvoidingCupIndex578 joint blocker, ∀ j : Fin 6,
    CupCapFirstJointSplit578 tree cup.1 (joint.saturation.capAt j)

theorem exists_blockerAvoidingCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) (blocker : Fin 6) :
    Nonempty (BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker) := by
  classical
  exact ⟨{
    cell := fun cup j ↦ Classical.choice
      (exists_cupCapFirstJointSplit578_general tree
        cup.mem_cupWitnesses (joint.saturation.capAt_mem j))
  }⟩

/-- Every row in the blocker-avoiding matrix is a prefix chain. -/
theorem BlockerAvoidingCupSixCapAddressMatrix578.row_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    (matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker)
    (cup : BlockerAvoidingCupIndex578 joint blocker) (j k : Fin 6) :
    (matrix.cell cup j).path <+: (matrix.cell cup k).path ∨
      (matrix.cell cup k).path <+: (matrix.cell cup j).path := by
  have hcupData := mem_capWitnesses.mp cup.mem_cupWitnesses
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

/-- Every column in the blocker-avoiding matrix is a prefix chain. -/
theorem BlockerAvoidingCupSixCapAddressMatrix578.column_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    (matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker)
    (first second : BlockerAvoidingCupIndex578 joint blocker) (j : Fin 6) :
    (matrix.cell first j).path <+: (matrix.cell second j).path ∨
      (matrix.cell second j).path <+: (matrix.cell first j).path := by
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hcapCard : 2 ≤ (joint.saturation.capAt j).card := by
    rw [hcapData.2.1]
    omega
  let capPath := tree.lowestSeparatingPath hcapData.1 hcapCard
  have hprefix (cup : BlockerAvoidingCupIndex578 joint blocker) :
      (matrix.cell cup j).path <+: capPath := by
    have hcupData := mem_capWitnesses.mp cup.mem_cupWitnesses
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

/-- A global common minimum for the complete blocker-avoiding matrix. -/
structure BlockerAvoidingCupSixCapCommonMinimum578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    (matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker) where
  row : BlockerAvoidingCupIndex578 joint blocker
  column : Fin 6
  minimal : ∀ cup j, (matrix.cell row column).path <+:
    (matrix.cell cup j).path

theorem BlockerAvoidingCupSixCapAddressMatrix578.commonMinimum_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    (matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker)
    [Nonempty (BlockerAvoidingCupIndex578 joint blocker)] :
    Nonempty (BlockerAvoidingCupSixCapCommonMinimum578 matrix) := by
  classical
  letI : Fintype (Finset (Fin n)) := Finset.fintype
  letI : Fintype (BlockerAvoidingCupIndex578 joint blocker) := Subtype.fintype _
  obtain ⟨row, column, hminimal⟩ := exists_globalPrefixMinimum_finiteMatrix
    (fun cup j ↦ (matrix.cell cup j).path)
    matrix.row_paths_comparable matrix.column_paths_comparable
  exact ⟨{ row := row, column := column, minimal := hminimal }⟩

/-- Strict false-direction descent from the blocker-family minimum localizes
the associated cup and cap block in the lower child. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.cell_union_subset_lower_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix)
    {cup : BlockerAvoidingCupIndex578 joint blocker} {j : Fin 6}
    {tail : List Bool}
    (hextends : (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: tail) :
    cup.1 ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.lower :=
  (matrix.cell cup j).allocated.subset_lower_of_path_eq_append_false
    (matrix.cell minimum.row minimum.column).lookup hextends

/-- Strict true-direction descent from the blocker-family minimum localizes
the associated cup and cap block in the upper child. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.cell_union_subset_upper_of_extends
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix)
    {cup : BlockerAvoidingCupIndex578 joint blocker} {j : Fin 6}
    {tail : List Bool}
    (hextends : (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path ++ true :: tail) :
    cup.1 ∪ joint.saturation.capAt j ⊆
      (matrix.cell minimum.row minimum.column).node.upper :=
  (matrix.cell cup j).allocated.subset_upper_of_path_eq_append_true
    (matrix.cell minimum.row minimum.column).lookup hextends

/-- Cross-corner collapse does not depend on the number of rows. -/
theorem indexBySix_crossCorners_eq_of_oppositeExtensions
    {ι : Type} (path : ι → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j)
    {i₀ : ι} {j₀ : Fin 6}
    (hminimum : ∀ i j, path i₀ j₀ <+: path i j)
    {i k : ι} {j l : Fin 6} {leftTail rightTail : List Bool}
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

/-- The witness-carrying one-sided/mixed address classification does not
depend on the number of rows. -/
theorem indexBySix_oneSided_or_oppositeExtensions
    {ι : Type} (path : ι → Fin 6 → List Bool)
    (hrow : ∀ i j k, path i j <+: path i k ∨ path i k <+: path i j)
    (hcolumn : ∀ i k j, path i j <+: path k j ∨ path k j <+: path i j)
    {i₀ : ι} {j₀ : Fin 6}
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
        indexBySix_crossCorners_eq_of_oppositeExtensions
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

/-- Exhaustive raw address classification for the complete
blocker-avoiding family.  Unlike the residual matrix, the mixed branch cannot
be collapsed to a distinguished-row plateau because no row is known to meet
every other row. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.localizedCaps_or_minimumColumn_or_mixedRectangle
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix) :
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card) ∨
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card) ∨
    (∃ j, ∀ cup, (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path) ∨
    ∃ first second j k leftTail rightTail,
      (matrix.cell first j).path =
        (matrix.cell minimum.row minimum.column).path ++ false :: leftTail ∧
      (matrix.cell second k).path =
        (matrix.cell minimum.row minimum.column).path ++ true :: rightTail ∧
      (matrix.cell first k).path =
        (matrix.cell minimum.row minimum.column).path ∧
      (matrix.cell second j).path =
        (matrix.cell minimum.row minimum.column).path := by
  classical
  rcases indexBySix_oneSided_or_oppositeExtensions
      (fun cup j ↦ (matrix.cell cup j).path)
      matrix.row_paths_comparable matrix.column_paths_comparable
      minimum.minimal with hleft | hright | hmixed
  · by_cases hall : ∀ j, ∃ cup tail,
        (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: tail
    · left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.lower := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨cup, tail, hstrict⟩ := hall j
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
      refine ⟨j, fun cup ↦ ?_⟩
      rcases hleft cup j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj cup tail hstrict).elim
  · by_cases hall : ∀ j, ∃ cup tail,
        (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: tail
    · right
      left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.upper := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨cup, tail, hstrict⟩ := hall j
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
      refine ⟨j, fun cup ↦ ?_⟩
      rcases hright cup j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj cup tail hstrict).elim
  · exact Or.inr (Or.inr (Or.inr hmixed))

/-! ## Exact consumers for the two deletion-escape branches -/

/-- A four-set already avoiding one saturated cap necessarily avoids a
second, distinct saturated cap.  This is the sharp six-column consequence of
the source-disjoint deletion branch. -/
theorem SixCapSaturation578.exists_other_disjointCap_of_card_eq_four
    {n : ℕ} {χ : TripleColoring n} {support cup : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hcard : cup.card = 4) (j : Fin 6)
    (hdisjoint : Disjoint cup (saturation.capAt j)) :
    ∃ k : Fin 6, k ≠ j ∧ Disjoint cup (saturation.capAt k) := by
  obtain ⟨i, k, hik, hi, hk⟩ :=
    exists_two_disjoint_capAt578_of_card_le_four saturation
      (vertices := cup) (by omega)
  by_cases hji : j = i
  · subst j
    exact ⟨k, hik.symm, hk⟩
  · exact ⟨i, Ne.symm hji, hi⟩

/-- A source-disjoint deletion row enters the complete family for its source
blocker and also avoids another cap column. -/
theorem SixCapVertexDeletionResidualLedger578.sourceDisjoint_has_otherBlocker
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hdisjoint : Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    ∃ indexed : BlockerAvoidingCupIndex578 joint j,
      ∃ k : Fin 6, k ≠ j ∧
        Disjoint indexed.1 (joint.saturation.capAt k) := by
  have hcup := (joint.ledger.mem_residualCupFamily.mp
    (ledger.cupAt j c).2).1
  have hcard := (mem_capWitnesses.mp hcup).2.1
  obtain ⟨k, hkj, hk⟩ :=
    joint.saturation.exists_other_disjointCap_of_card_eq_four
      hcard j hdisjoint
  exact ⟨(ledger.cupAt j c).toBlockerAvoiding hdisjoint, k, hkj, hk⟩

/-- If a blocker-avoiding cup and all six caps are local to the lower child
of the common-minimum node, every cell in that row strictly descends in the
false direction.  This turns the lower-local deletion escape into an exact
recursive seed rather than an unclassified row. -/
theorem BlockerAvoidingCupSixCapCommonMinimum578.row_strictLower_of_local
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    {matrix : BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker}
    (minimum : BlockerAvoidingCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (cup : BlockerAvoidingCupIndex578 joint blocker)
    (hcup : cup.1 ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∀ j : Fin 6, ∃ tail,
      (matrix.cell cup j).path =
        (matrix.cell minimum.row minimum.column).path ++ false :: tail := by
  intro j
  let base := matrix.cell minimum.row minimum.column
  let cell := matrix.cell cup j
  have hcapLower : joint.saturation.capAt j ⊆ base.node.lower :=
    (joint.saturation.capAt_subset_capSupport j).trans hcaps
  rcases list_eq_or_exists_firstStep_of_prefix (minimum.minimal cup j) with
    heq | ⟨direction, tail, hstep⟩
  · exfalso
    have hnode : base.node = cell.node := by
      have hlookup := cell.lookup
      rw [heq, base.lookup] at hlookup
      exact Option.some.inj hlookup
    apply cell.not_all_lower
    rw [← hnode]
    exact Finset.union_subset hcup hcapLower
  · cases direction with
    | false => exact ⟨tail, by simpa [base, cell] using hstep⟩
    | true =>
        exfalso
        have hcapUpper : joint.saturation.capAt j ⊆ base.node.upper :=
          Finset.subset_union_right.trans
            (minimum.cell_union_subset_upper_of_extends
              (by simpa [base, cell] using hstep))
        have hcapCard := (mem_capWitnesses.mp
          (joint.saturation.capAt_mem j)).2.1
        obtain ⟨x, hx⟩ : (joint.saturation.capAt j).Nonempty :=
          Finset.card_pos.mp (by omega)
        exact (Finset.disjoint_left.mp base.node.deep.disjoint)
          (hcapLower hx) (hcapUpper hx)

/-- The lower-local deletion branch in the original full residual matrix is
already a strict six-cell false descent. -/
theorem FullResidualCupSixCapCommonMinimum578.row_strictLower_of_local
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (cup : joint.ResidualCupIndex)
    (hcup : cup.1 ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∀ j : Fin 6, ∃ tail,
      (matrix.cell cup j).path =
        (matrix.cell minimum.row minimum.column).path ++ false :: tail := by
  intro j
  let base := matrix.cell minimum.row minimum.column
  let cell := matrix.cell cup j
  have hcapLower : joint.saturation.capAt j ⊆ base.node.lower :=
    (joint.saturation.capAt_subset_capSupport j).trans hcaps
  rcases list_eq_or_exists_firstStep_of_prefix (minimum.minimal cup j) with
    heq | ⟨direction, tail, hstep⟩
  · exfalso
    have hnode : base.node = cell.node := by
      have hlookup := cell.lookup
      rw [heq, base.lookup] at hlookup
      exact Option.some.inj hlookup
    apply cell.not_all_lower
    rw [← hnode]
    exact Finset.union_subset hcup hcapLower
  · cases direction with
    | false => exact ⟨tail, by simpa [base, cell] using hstep⟩
    | true =>
        exfalso
        have hcapUpper : joint.saturation.capAt j ⊆ base.node.upper :=
          Finset.subset_union_right.trans
            (minimum.cell_union_subset_upper_of_extends
              (by simpa [base, cell] using hstep))
        have hcapCard := (mem_capWitnesses.mp
          (joint.saturation.capAt_mem j)).2.1
        obtain ⟨x, hx⟩ : (joint.saturation.capAt j).Nonempty :=
          Finset.card_pos.mp (by omega)
        exact (Finset.disjoint_left.mp base.node.deep.disjoint)
          (hcapLower hx) (hcapUpper hx)

/-- Canonical lowest-separating paths make the residual-matrix cell and the
complete blocker-family cell agree whenever they index the same cup/cap
pair. -/
theorem BlockerAvoidingCupSixCapAddressMatrix578.cell_path_eq_fullResidual
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support} {blocker : Fin 6}
    (blockerMatrix :
      BlockerAvoidingCupSixCapAddressMatrix578 joint tree blocker)
    (residualMatrix : FullResidualCupSixCapAddressMatrix578 joint tree)
    (cup : joint.ResidualCupIndex)
    (hdisjoint : Disjoint cup.1 (joint.saturation.capAt blocker))
    (j : Fin 6) :
    (blockerMatrix.cell (cup.toBlockerAvoiding hdisjoint) j).path =
      (residualMatrix.cell cup j).path := by
  have hcupData := mem_capWitnesses.mp
    (joint.ledger.mem_residualCupFamily.mp cup.2).1
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hunionSub : cup.1 ∪ joint.saturation.capAt j ⊆ support :=
    Finset.union_subset hcupData.1 hcapData.1
  have hunionCard : 2 ≤ (cup.1 ∪ joint.saturation.capAt j).card := by
    have hle := Finset.card_le_card
      (Finset.subset_union_left : cup.1 ⊆
        cup.1 ∪ joint.saturation.capAt j)
    rw [hcupData.2.1] at hle
    omega
  exact (blockerMatrix.cell
      (cup.toBlockerAvoiding hdisjoint) j).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard |>.trans
    ((residualMatrix.cell cup j).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard).symm

/-! ## Density witnesses enter the complete family -/

/-- The two blocker-avoiding density witnesses are actual rows of the new
matrix index.  This is the exact bridge missing from the residual matrix. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_two_blockerAvoidingCupIndices
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (blocker : Fin 6) :
    ∃ cup₁ cup₂ : BlockerAvoidingCupIndex578 joint blocker,
      ¬cup₁.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      ¬cup₂.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      Disjoint
        (sweepMiddlePair578 cup₁.1
          (mem_capWitnesses.mp cup₁.mem_cupWitnesses).2.1)
        (sweepMiddlePair578 cup₂.1
          (mem_capWitnesses.mp cup₂.mem_cupWitnesses).2.1) := by
  obtain ⟨cup₁, cup₂, hdisjoint₁, hdisjoint₂,
      hnotUpper₁, hnotUpper₂, hmiddle⟩ :=
    minimum.exists_two_disjoint_restrictedCupMiddlePairs
      hreservoir hcard hnoCup hnoCap hnoStrong hcaps blocker
  exact ⟨cup₁.toBlockerAvoiding hdisjoint₁,
    cup₂.toBlockerAvoiding hdisjoint₂, hnotUpper₁, hnotUpper₂, hmiddle⟩

/-! ## Information-preserving total reconnect -/

/-- Strengthen the total deletion reconnect by retaining `all_base` and
`all_meet` in its positive fan branch.  These are not new assumptions: their
failures are exactly the first two alternatives, and the proof below carries
the surviving proofs into the result instead of discarding them. -/
theorem FullResidualCupSixCapCommonMinimum578.deletionEscape_or_lowerEscape_or_allBaseMeetingFanDensity_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    (∃ j c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) ∨
    (∃ j c, (ledger.cupAt j c).1 ⊆
      (matrix.cell minimum.row minimum.column).node.lower) ∨
    ∃ hupper :
        (matrix.cell minimum.row minimum.column).node.upper.Nonempty,
      ∃ witness :
          AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper,
        ∃ j : Fin 6,
          5 ≤ (witness.fan.entries.filter fun p ↦
            Disjoint (ledger.cupAt p.1 p.2).1
              (joint.saturation.capAt j)).card ∧
          2 ≤ (witness.fan.deficitCupsAt j).card ∧
          ∃ cup₁ cup₂ : BlockerAvoidingCupIndex578 joint j,
            ¬cup₁.1 ⊆
              (matrix.cell minimum.row minimum.column).node.upper ∧
            ¬cup₂.1 ⊆
              (matrix.cell minimum.row minimum.column).node.upper ∧
            Disjoint
              (sweepMiddlePair578 cup₁.1
                (mem_capWitnesses.mp cup₁.mem_cupWitnesses).2.1)
              (sweepMiddlePair578 cup₂.1
                (mem_capWitnesses.mp cup₂.mem_cupWitnesses).2.1) := by
  let base := matrix.cell minimum.row minimum.column
  have hnodeSub : base.node.lower ∪ base.node.upper ⊆ reservoir :=
    tree.splitAtPath_support_subset base.lookup
  have hnoCupNode :
      ¬ContainsCupSet χ (base.node.lower ∪ base.node.upper) 5 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hnodeSub)
  have hnoCapNode :
      ¬ContainsCapSet χ (base.node.lower ∪ base.node.upper) 7 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      (hnodeSub.trans Finset.subset_union_right))
  have hupper : base.node.upper.Nonempty := by
    obtain ⟨x, hxUnion, hxNotLower⟩ :=
      Finset.not_subset.mp base.not_all_lower
    rcases Finset.mem_union.mp (base.union_local hxUnion) with
      hxLower | hxUpper
    · exact (hxNotLower hxLower).elim
    · exact ⟨x, hxUpper⟩
  by_cases hmeet : ∀ j c, ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)
  · by_cases hbase : ∀ j c,
        (matrix.cell (ledger.cupAt j c) j).path = base.path
    · right
      right
      obtain ⟨fan⟩ := minimum.exists_nineOneSidedDeletionFan ledger
        hcaps hupper hnoCupNode hnoCapNode hbase hmeet
      let witness :
          AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum hupper :=
        { fan := fan, all_base := hbase, all_meet := hmeet }
      obtain ⟨j, hj, cup₁, cup₂, hdisjoint₁, hdisjoint₂,
          hnotUpper₁, hnotUpper₂, hmiddle⟩ :=
        fan.exists_fiveDeficitColumn_and_two_disjoint_restrictedCupMiddlePairs
          hreservoir hcard hnoCup hnoCap hnoStrong hcaps
      exact ⟨hupper, witness, j, hj,
        witness.two_le_deficitCupsAt_card hcaps j hj,
        cup₁.toBlockerAvoiding hdisjoint₁,
        cup₂.toBlockerAvoiding hdisjoint₂,
        hnotUpper₁, hnotUpper₂, hmiddle⟩
    · right
      left
      push Not at hbase
      obtain ⟨j, c, hne⟩ := hbase
      refine ⟨j, c, ?_⟩
      rcases minimum.cup_subset_lower_or_rowPlateau_of_capSupport_subset_lower
          hcaps (ledger.cupAt j c) with hlower | hplateau
      · exact hlower
      · exact (hne (hplateau j)).elim
  · left
    push Not at hmeet
    exact hmeet

/-! ## Strengthened total reconnect -/

/-- The exact payload of the source-disjoint branch after using all six cap
columns. -/
structure TwoBlockerDeletionEscape578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint) where
  sourceColumn : Fin 6
  source : {x : Fin n // x ∈ joint.saturation.capAt sourceColumn}
  otherColumn : Fin 6
  other_ne_source : otherColumn ≠ sourceColumn
  disjoint_source : Disjoint (ledger.cupAt sourceColumn source).1
    (joint.saturation.capAt sourceColumn)
  disjoint_other : Disjoint (ledger.cupAt sourceColumn source).1
    (joint.saturation.capAt otherColumn)

/-- The exact payload of the lower-local branch: one residual row and all six
of its cap cells strictly descend into the large lower child. -/
structure StrictLowerDeletionEscape578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix) where
  sourceColumn : Fin 6
  source : {x : Fin n // x ∈ joint.saturation.capAt sourceColumn}
  strict : ∀ j : Fin 6, ∃ tail,
    (matrix.cell (ledger.cupAt sourceColumn source) j).path =
      (matrix.cell minimum.row minimum.column).path ++ false :: tail

/-- The information-preserving positive fan/density payload. -/
structure AllBaseMeetingFanDensityOutcome578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix) where
  upper_nonempty :
    (matrix.cell minimum.row minimum.column).node.upper.Nonempty
  witness : AllBaseMeetingNineOneSidedDeletionFan578 ledger minimum
    upper_nonempty
  blocker : Fin 6
  five_entries : 5 ≤ (witness.fan.deficitEntriesAt blocker).card
  two_distinct_rows : 2 ≤ (witness.fan.deficitCupsAt blocker).card
  densityCup₁ : BlockerAvoidingCupIndex578 joint blocker
  densityCup₂ : BlockerAvoidingCupIndex578 joint blocker
  densityCup₁_not_upper : ¬densityCup₁.1 ⊆
    (matrix.cell minimum.row minimum.column).node.upper
  densityCup₂_not_upper : ¬densityCup₂.1 ⊆
    (matrix.cell minimum.row minimum.column).node.upper
  middle_disjoint : Disjoint
    (sweepMiddlePair578 densityCup₁.1
      (mem_capWitnesses.mp densityCup₁.mem_cupWitnesses).2.1)
    (sweepMiddlePair578 densityCup₂.1
      (mem_capWitnesses.mp densityCup₂.mem_cupWitnesses).2.1)

/-- The final exact reconnect for this experiment.  The two formerly raw
escape branches are replaced by a two-blocker cup and a strict recursive
descent, while the fan branch retains both its distinct selected rows and the
independent density witnesses. -/
theorem FullResidualCupSixCapCommonMinimum578.twoBlocker_or_strictLower_or_fanDensity_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    Nonempty (TwoBlockerDeletionEscape578 ledger) ∨
    Nonempty (StrictLowerDeletionEscape578 ledger minimum) ∨
    Nonempty (AllBaseMeetingFanDensityOutcome578 ledger minimum) := by
  rcases minimum.deletionEscape_or_lowerEscape_or_allBaseMeetingFanDensity_at_32
      ledger hreservoir hcard hnoCup hnoCap hnoStrong hcaps with
    hsource | hlower | hfan
  · obtain ⟨j, c, hj⟩ := hsource
    have hcup := (joint.ledger.mem_residualCupFamily.mp
      (ledger.cupAt j c).2).1
    have hcupCard := (mem_capWitnesses.mp hcup).2.1
    obtain ⟨k, hkj, hk⟩ :=
      joint.saturation.exists_other_disjointCap_of_card_eq_four
        hcupCard j hj
    exact Or.inl ⟨{
      sourceColumn := j
      source := c
      otherColumn := k
      other_ne_source := hkj
      disjoint_source := hj
      disjoint_other := hk
    }⟩
  · obtain ⟨j, c, hlocal⟩ := hlower
    exact Or.inr (Or.inl ⟨{
      sourceColumn := j
      source := c
      strict := minimum.row_strictLower_of_local hcaps
        (ledger.cupAt j c) hlocal
    }⟩)
  · obtain ⟨hupper, witness, blocker, hfive, htwo,
        cup₁, cup₂, hnotUpper₁, hnotUpper₂, hmiddle⟩ := hfan
    exact Or.inr (Or.inr ⟨{
      upper_nonempty := hupper
      witness := witness
      blocker := blocker
      five_entries := hfive
      two_distinct_rows := htwo
      densityCup₁ := cup₁
      densityCup₂ := cup₂
      densityCup₁_not_upper := hnotUpper₁
      densityCup₂_not_upper := hnotUpper₂
      middle_disjoint := hmiddle
    }⟩)

/-! ## Reconnection to the exact color-dual gate -/

/-- The complete tight-state payload produced after the fourth-cup and
two-spine alternatives have failed. -/
structure TightDeficitDensityReduction578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  one_spine : (joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal).card = 1
  tree : DecompositionTree χ support
  matrix : FullResidualCupSixCapAddressMatrix578 joint tree
  minimum : FullResidualCupSixCapCommonMinimum578 matrix
  ledger : SixCapVertexDeletionResidualLedger578 joint
  outcome :
    (¬joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) ∨
    Nonempty (TwoBlockerDeletionEscape578 ledger) ∨
    Nonempty (StrictLowerDeletionEscape578 ledger minimum) ∨
    Nonempty (AllBaseMeetingFanDensityOutcome578 ledger minimum)

/-- Exact `32`-vertex color-dual reduction with no hidden fan hypotheses.
After the already-named fourth-cup and two-spine branches, the tight state
contains a full common-minimum matrix, its 24-entry deletion ledger, and the
strengthened total outcome above (unless the six-cap support is not lower at
that minimum). -/
theorem exists_fourthDisjointCup_or_twoFullSpines_or_tightDeficitDensityReduction_at_32
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
      Nonempty (TightDeficitDensityReduction578 joint) := by
  have hnoCupReservoir : ¬ContainsCupSet χ reservoir 5 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
      Finset.subset_union_right)
  rcases exists_fourthDisjointCup_or_twoFullSpines_or_fullResidualCommonMinimum_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | ⟨joint, hmany | htight⟩
  · exact Or.inl hfourth
  · exact Or.inr ⟨joint, Or.inl hmany⟩
  · obtain ⟨hone, tree, matrix, hminimum⟩ := htight
    obtain ⟨minimum⟩ := hminimum
    obtain ⟨ledger⟩ := exists_sixCapVertexDeletionResidualLedger578_at_32
      joint hreservoir hcard hnoCap hnoStrong hone
    by_cases hcaps : joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower
    · have houtcome := minimum.twoBlocker_or_strictLower_or_fanDensity_at_32
        ledger hreservoir hcard hnoCupReservoir hnoCap hnoStrong hcaps
      exact Or.inr ⟨joint, Or.inr ⟨{
        one_spine := hone
        tree := tree
        matrix := matrix
        minimum := minimum
        ledger := ledger
        outcome := Or.inr houtcome
      }⟩⟩
    · exact Or.inr ⟨joint, Or.inr ⟨{
        one_spine := hone
        tree := tree
        matrix := matrix
        minimum := minimum
        ledger := ledger
        outcome := Or.inl hcaps
      }⟩⟩

end ErdosSzekeres

end
