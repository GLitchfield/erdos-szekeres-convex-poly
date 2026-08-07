module

public import ErdosSzekeres.StructuralChargingRankTwoGenealogy

@[expose] public section

/-!
# Conserved sweep-gap tokens

Every nonempty finite sweep support has exactly one token per vertex: the
minimum vertex owns a sentinel, and every other vertex owns its unique
immediately preceding adjacency.  Consequently, for disjoint nonempty child
supports, the two child token families merge bijectively into the parent token
family.  Child gaps are transported rather than added again at the parent.

This is exact conservation bookkeeping.  It does not attach higher-rank
Pascal demand to a token or bound the length of a token's history.
-/

namespace ErdosSzekeres

noncomputable section

/-- The sweep adjacencies inside a fixed support. -/
abbrev SweepAdjacency {n : ℕ} (support : Finset (Fin n)) :=
  {span : SweepSpanEndpoints n // span.IsAdjacentIn support}

noncomputable instance sweepAdjacencyFintype {n : ℕ}
    (support : Finset (Fin n)) : Fintype (SweepAdjacency support) :=
  Fintype.ofFinite _

/-- One token for every adjacency, together with a sentinel for the minimum. -/
abbrev SweepGapToken {n : ℕ} (support : Finset (Fin n)) :=
  SweepAdjacency support ⊕ Unit

/-- An actual support vertex regarded as the owner of a conserved token. -/
abbrev RetainedVertexOwner {n : ℕ} (support : Finset (Fin n)) :=
  {q : Fin n // q ∈ support}

/-- A gap is owned by its right endpoint; the sentinel is owned by the
support minimum. -/
def SweepGapToken.owner {n : ℕ} {support : Finset (Fin n)}
    (hsupport : support.Nonempty) :
    SweepGapToken support → RetainedVertexOwner support
  | .inl gap => ⟨gap.1.right, gap.2.2.2.1⟩
  | .inr _ => ⟨support.min' hsupport, support.min'_mem hsupport⟩

/-- Distinct gap-or-sentinel tokens have distinct actual vertex owners. -/
theorem SweepGapToken.owner_injective {n : ℕ}
    {support : Finset (Fin n)} (hsupport : support.Nonempty) :
    Function.Injective (SweepGapToken.owner hsupport) := by
  intro first second heq
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          congr 1
          apply Subtype.ext
          exact SweepSpanEndpoints.IsAdjacentIn.eq_of_right_eq
            first.2 second.2 (congrArg Subtype.val heq)
      | inr second =>
          exfalso
          have hright : first.1.right = support.min' hsupport :=
            congrArg Subtype.val heq
          have hminLe : support.min' hsupport ≤ first.1.left :=
            support.min'_le first.1.left first.2.2.1
          have hlt := first.2.1
          rw [hright] at hlt
          exact (not_lt_of_ge hminLe hlt).elim
  | inr first =>
      cases second with
      | inl second =>
          exfalso
          have hright : support.min' hsupport = second.1.right :=
            congrArg Subtype.val heq
          have hminLe : support.min' hsupport ≤ second.1.left :=
            support.min'_le second.1.left second.2.2.1
          have hlt := second.2.1
          rw [← hright] at hlt
          exact (not_lt_of_ge hminLe hlt).elim
      | inr second => rfl

/-- Every support vertex owns either its preceding gap or the sentinel. -/
theorem SweepGapToken.owner_surjective {n : ℕ}
    {support : Finset (Fin n)} (hsupport : support.Nonempty) :
    Function.Surjective (SweepGapToken.owner hsupport) := by
  intro owner
  by_cases hminimum : owner.1 = support.min' hsupport
  · refine ⟨.inr (), ?_⟩
    apply Subtype.ext
    exact hminimum.symm
  · have hminLe : support.min' hsupport ≤ owner.1 :=
      support.min'_le owner.1 owner.2
    have hminNe : support.min' hsupport ≠ owner.1 :=
      fun heq => hminimum heq.symm
    have hminLt : support.min' hsupport < owner.1 :=
      lt_of_le_of_ne hminLe hminNe
    let prior := support.filter (fun q => q < owner.1)
    have hprior : prior.Nonempty := by
      exact ⟨support.min' hsupport, Finset.mem_filter.mpr
        ⟨support.min'_mem hsupport, hminLt⟩⟩
    let predecessor := prior.max' hprior
    let span : SweepSpanEndpoints n := ⟨predecessor, owner.1⟩
    have hadjacent : span.IsAdjacentIn support := by
      have hpredMem : predecessor ∈ prior := prior.max'_mem hprior
      have hpredData := Finset.mem_filter.mp hpredMem
      change predecessor < owner.1 ∧ predecessor ∈ support ∧
        owner.1 ∈ support ∧
          ∀ q ∈ support, ¬(predecessor < q ∧ q < owner.1)
      refine ⟨hpredData.2, hpredData.1, owner.2, ?_⟩
      intro q hqSupport hbetween
      have hqPrior : q ∈ prior :=
        Finset.mem_filter.mpr ⟨hqSupport, hbetween.2⟩
      have hqLe : q ≤ predecessor := prior.le_max' q hqPrior
      exact (not_lt_of_ge hqLe hbetween.1).elim
    refine ⟨.inl ⟨span, hadjacent⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Gap-or-sentinel tokens are exactly the actual vertices of a nonempty
support, with the displayed map preserving the owner. -/
noncomputable def sweepGapTokenOwnerEquiv {n : ℕ}
    {support : Finset (Fin n)} (hsupport : support.Nonempty) :
    SweepGapToken support ≃ RetainedVertexOwner support :=
  Equiv.ofBijective (SweepGapToken.owner hsupport)
    ⟨SweepGapToken.owner_injective hsupport,
      SweepGapToken.owner_surjective hsupport⟩

/-- There is exactly one conserved token per actual support vertex. -/
theorem sweepGapToken_card {n : ℕ} {support : Finset (Fin n)}
    (hsupport : support.Nonempty) :
    Fintype.card (SweepGapToken support) = support.card := by
  simpa using Fintype.card_congr (sweepGapTokenOwnerEquiv hsupport)

/-- A nonempty support has exactly one fewer adjacency than vertices. -/
theorem sweepAdjacency_card {n : ℕ} {support : Finset (Fin n)}
    (hsupport : support.Nonempty) :
    Fintype.card (SweepAdjacency support) = support.card - 1 := by
  have htoken := sweepGapToken_card hsupport
  change Fintype.card (SweepAdjacency support ⊕ Unit) =
    support.card at htoken
  rw [Fintype.card_sum, Fintype.card_unit] at htoken
  omega

/-- Include a child-owned vertex in the union support. -/
def retainedVertexOwnerOfChild {n : ℕ}
    {lower upper : Finset (Fin n)} :
    RetainedVertexOwner lower ⊕ RetainedVertexOwner upper →
      RetainedVertexOwner (lower ∪ upper)
  | .inl q => ⟨q.1, Finset.mem_union_left upper q.2⟩
  | .inr q => ⟨q.1, Finset.mem_union_right lower q.2⟩

theorem retainedVertexOwnerOfChild_injective {n : ℕ}
    {lower upper : Finset (Fin n)} (hdisjoint : Disjoint lower upper) :
    Function.Injective
      (retainedVertexOwnerOfChild (lower := lower) (upper := upper)) := by
  intro first second heq
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          congr 1
          apply Subtype.ext
          exact congrArg
            (fun q : RetainedVertexOwner (lower ∪ upper) => q.1) heq
      | inr second =>
          exfalso
          have hval : first.1 = second.1 :=
            congrArg
              (fun q : RetainedVertexOwner (lower ∪ upper) => q.1) heq
          exact (Finset.disjoint_left.mp hdisjoint first.2
            (hval ▸ second.2)).elim
  | inr first =>
      cases second with
      | inl second =>
          exfalso
          have hval : first.1 = second.1 :=
            congrArg
              (fun q : RetainedVertexOwner (lower ∪ upper) => q.1) heq
          exact (Finset.disjoint_left.mp hdisjoint second.2
            (hval.symm ▸ first.2)).elim
      | inr second =>
          congr 1
          apply Subtype.ext
          exact congrArg
            (fun q : RetainedVertexOwner (lower ∪ upper) => q.1) heq

theorem retainedVertexOwnerOfChild_surjective {n : ℕ}
    {lower upper : Finset (Fin n)} :
    Function.Surjective
      (retainedVertexOwnerOfChild (lower := lower) (upper := upper)) := by
  intro owner
  rcases Finset.mem_union.mp owner.2 with hlower | hupper
  · refine ⟨.inl ⟨owner.1, hlower⟩, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨.inr ⟨owner.1, hupper⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Disjoint child-owner families are exactly the owner family of their
union. -/
def retainedVertexOwnerSumEquivUnion {n : ℕ}
    {lower upper : Finset (Fin n)} (hdisjoint : Disjoint lower upper) :
    RetainedVertexOwner lower ⊕ RetainedVertexOwner upper ≃
      RetainedVertexOwner (lower ∪ upper) :=
  Equiv.ofBijective retainedVertexOwnerOfChild
    ⟨retainedVertexOwnerOfChild_injective hdisjoint,
      retainedVertexOwnerOfChild_surjective⟩

/-- The actual union vertex owned by a token coming from either child. -/
def sweepGapTokenOwnerOfChild {n : ℕ}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty) :
    SweepGapToken lower ⊕ SweepGapToken upper →
      RetainedVertexOwner (lower ∪ upper)
  | .inl token => retainedVertexOwnerOfChild (.inl (token.owner hlower))
  | .inr token => retainedVertexOwnerOfChild (.inr (token.owner hupper))

/-- The two child token families merge without loss or duplication into the
parent token family.  The equivalence is mediated by actual vertex owners. -/
noncomputable def sweepGapTokenMergeEquiv {n : ℕ}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) :
    SweepGapToken lower ⊕ SweepGapToken upper ≃
      SweepGapToken (lower ∪ upper) :=
  ((sweepGapTokenOwnerEquiv hlower).sumCongr
      (sweepGapTokenOwnerEquiv hupper)).trans
    ((retainedVertexOwnerSumEquivUnion hdisjoint).trans
      (sweepGapTokenOwnerEquiv
        (hlower.mono (Finset.subset_union_left))).symm)

/-- The merge transports a child token to the parent token with the same
actual vertex owner. -/
theorem sweepGapTokenMergeEquiv_owner {n : ℕ}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper)
    (token : SweepGapToken lower ⊕ SweepGapToken upper) :
    (sweepGapTokenMergeEquiv hlower hupper hdisjoint token).owner
        (hlower.mono (Finset.subset_union_left)) =
      sweepGapTokenOwnerOfChild hlower hupper token := by
  let hunion : (lower ∪ upper).Nonempty :=
    hlower.mono Finset.subset_union_left
  change (sweepGapTokenOwnerEquiv hunion)
      ((sweepGapTokenOwnerEquiv hunion).symm
        (retainedVertexOwnerOfChild
          ((sweepGapTokenOwnerEquiv hlower).sumCongr
            (sweepGapTokenOwnerEquiv hupper) token))) =
      sweepGapTokenOwnerOfChild hlower hupper token
  rw [Equiv.apply_symm_apply]
  cases token <;> rfl

/-- Regard a hidden child gap as the corresponding child adjacency token. -/
def AllHiddenGapSource.toChildSweepGapToken {n : ℕ}
    {lower upper : Finset (Fin n)} :
    AllHiddenGapSource lower upper →
      SweepGapToken lower ⊕ SweepGapToken upper
  | .inl source =>
      .inr (.inl ⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩)
  | .inr source =>
      .inl (.inl ⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩)

/-- Regard a parent crossing gap as an ordinary parent adjacency token. -/
def ParentCrossingGap.toSweepGapToken {n : ℕ}
    {lower upper : Finset (Fin n)}
    (target : ParentCrossingGap lower upper) :
    SweepGapToken (lower ∪ upper) :=
  .inl ⟨target.1, (mem_parentCrossingGaps_iff.mp target.2).1⟩

/-- The owner-mediated merge agrees with the already compiled canonical
hidden-gap transport. -/
theorem sweepGapTokenMergeEquiv_hiddenSource {n : ℕ}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper)
    (source : AllHiddenGapSource lower upper) :
    sweepGapTokenMergeEquiv hlower hupper hdisjoint
        source.toChildSweepGapToken =
      (allHiddenGapSourceEntering source).toSweepGapToken := by
  apply SweepGapToken.owner_injective
    (hlower.mono Finset.subset_union_left)
  rw [sweepGapTokenMergeEquiv_owner]
  apply Subtype.ext
  cases source with
  | inl source =>
      exact source.enteringParentCrossingGap_right.symm
  | inr source =>
      exact source.enteringParentCrossingGap_right.symm

end

end ErdosSzekeres

end
