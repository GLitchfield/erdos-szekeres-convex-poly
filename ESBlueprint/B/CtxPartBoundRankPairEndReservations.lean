import ESBlueprint.B.CtxPartTrackedRankPairEndReservations
import ESBlueprint.B.CtxOneLevelRankPairPotentialBound

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- With a preserved actual marker on the side opposite a cut and chosen global at most four, bound every fuel and the full recursive part by the source rank-pair budget after reserving endpoint rows and columns for source-active removed children outside the active part. The exact union is charged without loss; if the part has active children, the separate left and right rank-union charges lose at most one. Uses the actual-marker rank-pair potential and the end-reservation theorem, without activity assumptions on untracked children or restrictions on old maxima.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_bound_rank_pair_end_reservations (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNt : σ.sideAt N = t) (hx : x ∈ σ.extPositions N)
  (hglobal : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m : ℕ) (L R : Finset ℕ) :
  let τ := σ.part keep s m
  let global := fun (ρ : Ctx.Context) => match s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let interval := fun (ρ : Ctx.Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt s 0 p + 1) (global ρ - 1 - ρ.rightExt s 0 p)
  let pairs := fun (ρ : Ctx.Context) (p : ℕ) =>
    ((interval ρ p).product (interval ρ p)).filter (fun z => z.1 ≤ z.2)
  let sourcePairs := (active σ).biUnion (pairs σ)
  let rows := L.biUnion (fun p => ({σ.leftExt s 0 p + 1} : Finset ℕ).product (interval σ p))
  let columns := R.biUnion (fun p => (interval σ p).product ({global σ - 1 - σ.rightExt s 0 p} : Finset ℕ))
  let reserved := rows ∪ columns
  let leftRanks := L.biUnion (interval σ)
  let rightRanks := R.biUnion (interval σ)
  (∀ p ∈ L, p ∈ active σ ∧ p ∉ keep) →
  (∀ p ∈ R, p ∈ active σ ∧ p ∉ keep) →
  (∀ p ∈ L, ∀ q ∈ active τ, p < q) →
  (∀ p ∈ R, ∀ q ∈ active τ, q < p) →
  (∀ fuel, Ctx.Context.boundFuel fuel τ + reserved.card ≤ sourcePairs.card) ∧
    τ.bound + reserved.card ≤ sourcePairs.card ∧
    ((active τ).Nonempty →
      (∀ fuel, Ctx.Context.boundFuel fuel τ + leftRanks.card + rightRanks.card ≤ sourcePairs.card + 1) ∧
      τ.bound + leftRanks.card + rightRanks.card ≤ sourcePairs.card + 1) := by
  classical
  have hPartPos : ∀ r j w, (σ.part keep s m).letterAt r = Letter.ext j w → 1 ≤ j := by
    intro r j w hr
    have hrl : r < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part keep s m)
        (show (σ.part keep s m).word.length ≤ r by rw [part_word_length]; omega)
      rw [hn] at hr
      cases hr
    cases he : σ.letterAt r with
    | child =>
      rw [part_letterAt_of_child σ keep s m hrl he] at hr
      split at hr
      · cases hr
      · cases hr; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ keep s m hrl he] at hr
      cases hr; omega
  let τ := σ.part keep s m
  let G (ρ : Context) := match s with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (p : ℕ) := Finset.Icc (ρ.leftExt s 0 p + 1) (G ρ - 1 - ρ.rightExt s 0 p)
  let Tri (ρ : Context) (p : ℕ) := ((I ρ p).product (I ρ p)).filter (fun z => z.1 ≤ z.2)
  let F := active σ
  let Q := active τ
  let S := F.biUnion (Tri σ)
  let T := Q.biUnion (Tri τ)
  let Rows := L.biUnion (fun p => ({σ.leftExt s 0 p + 1} : Finset ℕ).product (I σ p))
  let Cols := R.biUnion (fun p => (I σ p).product ({G σ - 1 - σ.rightExt s 0 p} : Finset ℕ))
  let E := Rows ∪ Cols
  let LR := L.biUnion (I σ)
  let RR := R.biUnion (I σ)
  change (∀ p ∈ L, p ∈ F ∧ p ∉ keep) → (∀ p ∈ R, p ∈ F ∧ p ∉ keep) →
    (∀ p ∈ L, ∀ q ∈ Q, p < q) → (∀ p ∈ R, ∀ q ∈ Q, q < p) →
    (∀ fuel, boundFuel fuel τ + E.card ≤ S.card) ∧ τ.bound + E.card ≤ S.card ∧
    (Q.Nonempty → (∀ fuel, boundFuel fuel τ + LR.card + RR.card ≤ S.card + 1) ∧
      τ.bound + LR.card + RR.card ≤ S.card + 1)
  intro hL hR hleft hright
  have hF : ∀ p ∈ F, p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    intro p hp
    obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hp
    exact ⟨List.mem_toFinset.mp hc, ha⟩
  have hQ : ∀ p ∈ Q, p ∈ τ.childPositions ∧ 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
    intro p hp
    obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hp
    exact ⟨List.mem_toFinset.mp hc, ha⟩
  have hQF : Q ⊆ F := by
    intro p hp
    obtain ⟨hc, ha⟩ := hQ p hp
    change p ∈ (σ.part keep s m).childPositions at hc
    rw [part_childPositions] at hc
    have hl := ctx_part_limits_le σ keep s m p p
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_filter.mp hc).1,
      Nat.lt_of_lt_of_le ha.1 hl.1, Nat.lt_of_lt_of_le ha.2 hl.2⟩
  have hNpos : 1 ≤ N := one_le_of_mem_levels hN
  have hNτ : N + 1 ∈ τ.levels := by
    change N + 1 ∈ (σ.part keep s m).levels
    simp only [part_levels, List.mem_cons, List.mem_map]
    right
    exact ⟨N, hN, rfl⟩
  have hNtτ : τ.sideAt (N + 1) = t := (part_sideAt_succ σ keep s m hNpos).trans hNt
  have hxτ : x ∈ τ.extPositions (N + 1) := by
    change x ∈ (σ.part keep s m).extPositions (N + 1)
    rw [part_extPositions_succ σ keep s m hNpos]
    exact hx
  have hBounds : (∀ fuel, boundFuel fuel τ ≤ T.card) ∧ τ.bound ≤ T.card :=
    ctx_one_level_rank_pair_potential_bound τ hPartPos t s (Ne.symm hne) (N + 1) x
      hNτ hNtτ hxτ hglobal
  have hReservations := ctx_part_tracked_rank_pair_end_reservations σ hpositive s keep m F Q L R
    hF hQ hQF hL hR hleft hright
  have hCharge : T.card + E.card ≤ S.card := hReservations.2.2.1
  have hEndCharge (hQne : Q.Nonempty) : T.card + LR.card + RR.card ≤ S.card + 1 :=
    (hReservations.2.2.2.2.2 hQne).2
  refine ⟨?_, ?_, ?_⟩
  · intro fuel
    exact (Nat.add_le_add_right (hBounds.1 fuel) E.card).trans hCharge
  · exact (Nat.add_le_add_right hBounds.2 E.card).trans hCharge
  · intro hQne
    constructor
    · intro fuel
      have hb := hBounds.1 fuel
      have hc := hEndCharge hQne
      omega
    · have hb := hBounds.2
      have hc := hEndCharge hQne
      omega

end ErdosSzekeres
