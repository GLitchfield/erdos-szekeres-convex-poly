import ESBlueprint.B.CtxActualMarkerRankPairUnionNineBound
import ESBlueprint.B.CtxPartPruningHistoryTransport

namespace ErdosSzekeres

/-- For an actual indexed marker on an axis of global at most five, the active ordered-rank-pair unions of any binary child pruning share the same source envelope and their union has cardinal at most nine.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_actual_marker_rank_pair_union_nine_bound, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_binary_pruning_actual_marker_rank_pair_union_nine_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (t : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hNt : σ.sideAt N = t) (hx : x ∈ σ.extPositions N) (hglobal : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (color : ℕ → ℕ) : let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun p => color p = c); let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p); let interval : ℕ → ℕ → Finset ℕ := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun p => ((interval c p).product (interval c p)).filter (fun z => z.1 ≤ z.2)); ((pairs 0) ∪ (pairs 1)).card ≤ 9 := by
  classical
  let support : ℕ → List ℕ := fun c =>
    σ.childPositions.filter (fun p => color p = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global := match t with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c =>
    (group c).childPositions.toFinset.filter
      (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let interval : ℕ → ℕ → Finset ℕ := fun c p =>
    Finset.Icc ((group c).leftExt t 0 p + 1)
      (global - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) :=
    (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun p => Q (interval c p))
  let sourceActive := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let sourceInterval (p : ℕ) :=
    Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let sourcePairs := sourceActive.biUnion (fun p => Q (sourceInterval p))
  change ((pairs 0) ∪ (pairs 1)).card ≤ 9
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh : (group c).childPositions =
        σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive
        (support c) Ctx.Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hLimits (c p q : ℕ) :
      (group c).cupLimit p q = σ.cupLimit p q ∧
        (group c).capLimit p q = σ.capLimit p q :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.2.1 p q
  have hPure (c p : ℕ) :
      (group c).leftExt t 0 p = σ.leftExt t 0 p ∧
        (group c).rightExt t 0 p = σ.rightExt t 0 p :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.1 t 0 p
  have hActive (c p : ℕ) : p ∈ active c ↔
      p ∈ sourceActive ∧ color p = c := by
    simp only [active, sourceActive, Finset.mem_filter, List.mem_toFinset,
      hChild, (hLimits c p p).1, (hLimits c p p).2]
    tauto
  have hInterval (c p : ℕ) : interval c p = sourceInterval p := by
    simp only [interval, sourceInterval, (hPure c p).1, (hPure c p).2]
  have hPairSub (c : ℕ) : pairs c ⊆ sourcePairs := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    apply Finset.mem_biUnion.mpr
    exact ⟨p, (hActive c p).mp hp |>.1, by simpa only [hInterval c p] using hz⟩
  have hUnionSub : pairs 0 ∪ pairs 1 ⊆ sourcePairs := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hPairSub 0 hz
    · exact hPairSub 1 hz
  have hSource := ctx_actual_marker_rank_pair_union_nine_bound
    σ t N x hN hNt hx hglobal
  change sourcePairs.card ≤ 9 at hSource
  exact (Finset.card_le_card hUnionSub).trans hSource

end ErdosSzekeres
