import ESBlueprint.B.CtxBinaryCapacityPairIntersectionSourceWitnesses

namespace ErdosSzekeres

/-- If the active low/high rank-pair intersection in the canonical binary capacity pruning has cardinality at least two, it contains two distinct ordered pairs, each equipped with explicit source-active low- and high-capacity witnesses whose original-history intervals contain both coordinates. This turns the exact companion residual from a cardinal obstruction into two concrete collision objects for the remaining geometric argument.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_binary_capacity_pair_intersection_source_witnesses
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_binary_capacity_pair_intersection_two_distinct_source_witnesses (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) :
  let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun q => match σ.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global : ℕ := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)))
  let sourceInterval : ℕ → Finset ℕ := fun q => Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q)
  let Witness : ℕ × ℕ → Prop := fun z => ∃ low high, low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧ 0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧ high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧ 0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧ z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧ z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high
  2 ≤ ((pairs 0) ∩ (pairs 1)).card → ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w ∧ Witness z ∧ Witness w := by
  classical
  let capacity : ℕ → ℕ := fun q => match s with
    | Ctx.Side.lower => σ.cupLimit q q
    | Ctx.Side.upper => σ.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c =>
    σ.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with
    word := (List.range σ.word.length).map (fun q => match σ.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global : ℕ := match t with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c =>
    (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q =>
    Finset.Icc ((group c).leftExt t 0 q + 1)
      (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun q =>
      (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)))
  let sourceInterval : ℕ → Finset ℕ := fun q =>
    Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q)
  let Witness : ℕ × ℕ → Prop := fun z => ∃ low high,
    low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧
      0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧
    high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧
      0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧
    z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧
      z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high
  change 2 ≤ ((pairs 0) ∩ (pairs 1)).card →
    ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1),
      z ≠ w ∧ Witness z ∧ Witness w
  intro hcard
  have hWitness :=
    ctx_binary_capacity_pair_intersection_source_witnesses σ hpositive s t
  change ∀ z ∈ (pairs 0) ∩ (pairs 1), Witness z at hWitness
  have hNonempty : ((pairs 0) ∩ (pairs 1)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hNonempty
  have hEraseNonempty : (((pairs 0) ∩ (pairs 1)).erase z).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hz]
    omega
  obtain ⟨w, hwErase⟩ := hEraseNonempty
  have hw := Finset.mem_erase.mp hwErase
  exact ⟨z, hz, w, hw.2, Ne.symm hw.1,
    hWitness z hz, hWitness w hw.2⟩

end ErdosSzekeres
