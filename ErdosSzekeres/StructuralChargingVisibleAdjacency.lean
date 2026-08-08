module

public import ErdosSzekeres.StructuralChargingRootCritical

@[expose] public section

/-!
# Visible child adjacencies and exact remainder accounting

A child adjacency is either preserved as a visible adjacency of that child or
is hidden by a vertex of the opposite child.  For a nonempty child this gives
an exact cardinal identity: visible adjacencies, hidden adjacencies, and the
minimum-vertex sentinel account for every child vertex exactly once.

Combining this identity with a published retained core rewrites the proposed
hidden-pivot payment as an equivalent lower bound on the retained core.  This
is arithmetic bookkeeping only; no injection from visible adjacencies into a
core is asserted here.
-/

namespace ErdosSzekeres

noncomputable section

/-- Lower-child adjacencies not hidden by an upper-child vertex. -/
abbrev VisibleLowerAdjacency {n : ℕ} (lower upper : Finset (Fin n)) :=
  {gap : SweepAdjacency lower //
    ¬IsHiddenLowerGap lower upper gap.1}

/-- Lower-child adjacencies hidden by an upper-child vertex. -/
abbrev HiddenLowerAdjacency {n : ℕ} (lower upper : Finset (Fin n)) :=
  {gap : SweepAdjacency lower //
    IsHiddenLowerGap lower upper gap.1}

/-- Upper-child adjacencies not hidden by a lower-child vertex. -/
abbrev VisibleUpperAdjacency {n : ℕ} (lower upper : Finset (Fin n)) :=
  {gap : SweepAdjacency upper //
    ¬IsHiddenUpperGap lower upper gap.1}

/-- Upper-child adjacencies hidden by a lower-child vertex. -/
abbrev HiddenUpperAdjacency {n : ℕ} (lower upper : Finset (Fin n)) :=
  {gap : SweepAdjacency upper //
    IsHiddenUpperGap lower upper gap.1}

noncomputable instance visibleLowerAdjacencyFintype {n : ℕ}
    (lower upper : Finset (Fin n)) :
    Fintype (VisibleLowerAdjacency lower upper) :=
  Fintype.ofFinite _

noncomputable instance hiddenLowerAdjacencyFintype {n : ℕ}
    (lower upper : Finset (Fin n)) :
    Fintype (HiddenLowerAdjacency lower upper) :=
  Fintype.ofFinite _

noncomputable instance visibleUpperAdjacencyFintype {n : ℕ}
    (lower upper : Finset (Fin n)) :
    Fintype (VisibleUpperAdjacency lower upper) :=
  Fintype.ofFinite _

noncomputable instance hiddenUpperAdjacencyFintype {n : ℕ}
    (lower upper : Finset (Fin n)) :
    Fintype (HiddenUpperAdjacency lower upper) :=
  Fintype.ofFinite _

/-- A hidden lower adjacency is exactly a right-colored hidden-gap source. -/
def hiddenLowerGapSourceEquivHiddenLowerAdjacency
    {n : ℕ} (lower upper : Finset (Fin n)) :
    HiddenGapSource lower upper .right ≃
      HiddenLowerAdjacency lower upper where
  toFun source :=
    ⟨⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩,
      mem_hiddenGapSources_iff.mp source.2⟩
  invFun gap :=
    ⟨gap.1.1, mem_hiddenGapSources_iff.mpr gap.2⟩
  left_inv source := by
    apply Subtype.ext
    rfl
  right_inv gap := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- A hidden upper adjacency is exactly a left-colored hidden-gap source. -/
def hiddenUpperGapSourceEquivHiddenUpperAdjacency
    {n : ℕ} (lower upper : Finset (Fin n)) :
    HiddenGapSource lower upper .left ≃
      HiddenUpperAdjacency lower upper where
  toFun source :=
    ⟨⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩,
      mem_hiddenGapSources_iff.mp source.2⟩
  invFun gap :=
    ⟨gap.1.1, mem_hiddenGapSources_iff.mpr gap.2⟩
  left_inv source := by
    apply Subtype.ext
    rfl
  right_inv gap := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Visible lower adjacencies, hidden lower adjacencies, and the sentinel
partition a nonempty lower child exactly. -/
theorem visibleLowerAdjacency_card_add_hidden_add_one
    {n : ℕ} {lower upper : Finset (Fin n)} (hlower : lower.Nonempty) :
    Fintype.card (VisibleLowerAdjacency lower upper) +
        Fintype.card (HiddenGapSource lower upper .right) + 1 =
      lower.card := by
  classical
  have hhiddenCard :
      Fintype.card (HiddenLowerAdjacency lower upper) =
        Fintype.card (HiddenGapSource lower upper .right) :=
    (Fintype.card_congr
      (hiddenLowerGapSourceEquivHiddenLowerAdjacency lower upper)).symm
  have hhiddenLe :
      Fintype.card (HiddenLowerAdjacency lower upper) ≤
        Fintype.card (SweepAdjacency lower) :=
    Fintype.card_subtype_le _
  rw [Fintype.card_subtype_compl, hhiddenCard,
    sweepAdjacency_card hlower]
  rw [hhiddenCard, sweepAdjacency_card hlower] at hhiddenLe
  have hlowerPos := hlower.card_pos
  omega

/-- Visible upper adjacencies, hidden upper adjacencies, and the sentinel
partition a nonempty upper child exactly. -/
theorem visibleUpperAdjacency_card_add_hidden_add_one
    {n : ℕ} {lower upper : Finset (Fin n)} (hupper : upper.Nonempty) :
    Fintype.card (VisibleUpperAdjacency lower upper) +
        Fintype.card (HiddenGapSource lower upper .left) + 1 =
      upper.card := by
  classical
  have hhiddenCard :
      Fintype.card (HiddenUpperAdjacency lower upper) =
        Fintype.card (HiddenGapSource lower upper .left) :=
    (Fintype.card_congr
      (hiddenUpperGapSourceEquivHiddenUpperAdjacency lower upper)).symm
  have hhiddenLe :
      Fintype.card (HiddenUpperAdjacency lower upper) ≤
        Fintype.card (SweepAdjacency upper) :=
    Fintype.card_subtype_le _
  rw [Fintype.card_subtype_compl, hhiddenCard,
    sweepAdjacency_card hupper]
  rw [hhiddenCard, sweepAdjacency_card hupper] at hhiddenLe
  have hupperPos := hupper.card_pos
  omega

/-- The hidden term in the lower identity is literally the cardinality of
the canonical entering-pivot seed. -/
theorem visibleLowerAdjacency_card_add_pivotSeed_add_one
    {n : ℕ} {lower upper : Finset (Fin n)} (hlower : lower.Nonempty) :
    Fintype.card (VisibleLowerAdjacency lower upper) +
        (hiddenGapEnteringPivotSeed lower upper .right).card + 1 =
      lower.card := by
  rw [hiddenGapEnteringPivotSeed_card]
  exact visibleLowerAdjacency_card_add_hidden_add_one hlower

/-- The color-dual visible identity uses the left-colored pivot seed. -/
theorem visibleUpperAdjacency_card_add_pivotSeed_add_one
    {n : ℕ} {lower upper : Finset (Fin n)} (hupper : upper.Nonempty) :
    Fintype.card (VisibleUpperAdjacency lower upper) +
        (hiddenGapEnteringPivotSeed lower upper .left).card + 1 =
      upper.card := by
  rw [hiddenGapEnteringPivotSeed_card]
  exact visibleUpperAdjacency_card_add_hidden_add_one hupper

/-- Paying the lower remainder with hidden lower pivots is equivalent to
fitting all visible lower adjacencies plus the sentinel into the retained
lower core. -/
theorem lower_remainder_le_hidden_iff_visible_add_one_le_core
    {n : ℕ} {lower upper core : Finset (Fin n)}
    (hlower : lower.Nonempty) (hcore : core ⊆ lower) :
    (lower \ core).card ≤
        Fintype.card (HiddenGapSource lower upper .right) ↔
      Fintype.card (VisibleLowerAdjacency lower upper) + 1 ≤ core.card := by
  have hpartition :=
    visibleLowerAdjacency_card_add_hidden_add_one
      (lower := lower) (upper := upper) hlower
  have hsplit := Finset.card_sdiff_add_card_eq_card hcore
  omega

/-- Color-dual remainder payment equivalence for an upper retained core. -/
theorem upper_remainder_le_hidden_iff_visible_add_one_le_core
    {n : ℕ} {lower upper core : Finset (Fin n)}
    (hupper : upper.Nonempty) (hcore : core ⊆ upper) :
    (upper \ core).card ≤
        Fintype.card (HiddenGapSource lower upper .left) ↔
      Fintype.card (VisibleUpperAdjacency lower upper) + 1 ≤ core.card := by
  have hpartition :=
    visibleUpperAdjacency_card_add_hidden_add_one
      (lower := lower) (upper := upper) hupper
  have hsplit := Finset.card_sdiff_add_card_eq_card hcore
  omega

end

end ErdosSzekeres

end
