import ESBlueprint.B.CtxTwoMarkerMixedCapacityPairOverlapExcessBound

namespace ErdosSzekeres

/-- In an exact two-marker chosen-global-five context with a capacity-three witness and opposite global at most five, if the canonical low/high active opposite ordered-rank-pair unions intersect in at most one pair, then every fuel approximation and the full context are at most eleven. The exact overlap-excess theorem reduces the bound to choose(global,2) plus the intersection cardinality, isolating two distinct pair collisions as the remaining mixed-support obstruction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_mixed_capacity_pair_overlap_excess_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_mixed_capacity_pair_intersection_one_eleven_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let color := fun p => if capacity p ≤ 2 then (0 : ℕ) else 1; let support := fun c => σ.childPositions.filter (fun p => color p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p); let interval := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p); let pairs := fun c => (active c).biUnion (fun p => (((interval c p).product (interval c p)).filter (fun z => z.1 ≤ z.2))); ((pairs 0) ∩ (pairs 1)).card ≤ 1 → (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 11) ∧ σ.bound ≤ 11 := by
  classical
  let C (p : ℕ) := match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let color (p : ℕ) := if C p ≤ 2 then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  let G := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
    (G - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change ((pairs 0) ∩ (pairs 1)).card ≤ 1 →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 11) ∧ σ.bound ≤ 11
  intro hinter
  have hh := ctx_two_marker_mixed_capacity_pair_overlap_excess_bound
    σ hpositive s t hne N M x y high hN hM hNM hNs hMs hx hy
    hchosenGlobal hchosen hhighmem hhigh
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      G.choose 2 + ((pairs 0) ∩ (pairs 1)).card) ∧
    σ.bound ≤ G.choose 2 + ((pairs 0) ∩ (pairs 1)).card at hh
  have hChoose : G.choose 2 ≤ 10 := by
    have hc := Nat.choose_le_choose 2 hopposite
    simpa only [G] using hc
  constructor
  · intro fuel
    exact (hh.1 fuel).trans (by omega)
  · exact hh.2.trans (by omega)

end ErdosSzekeres
