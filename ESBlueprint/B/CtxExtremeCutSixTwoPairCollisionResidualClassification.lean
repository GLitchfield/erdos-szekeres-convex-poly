import ESBlueprint.B.CtxExtremeCutSixTwelveOfPairIntersectionOne

namespace ErdosSzekeres

/-- For an extreme chosen-kept cut at k six with a chosen-capacity-three companion witness, either every independent-fuel and full cut sum is at most twelve, or the canonical active low/high opposite ordered-rank-pair unions contain two explicit distinct shared pairs. This converts the exact pair-intersection cardinality obstruction into concrete witnesses for subsequent interval geometry.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_extreme_cut_six_twelve_of_pair_intersection_one
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_two_pair_collision_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hm : m + 2 = σ.k) (hk : σ.k = 6) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) : let A : Ctx.Context := σ.part keep s m; let B : Ctx.Context := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧ A.bound + B.bound ≤ 12) ∨ ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w := by
  classical
  cases s <;> cases t
  · exact (hne rfl).elim
  · let rest := σ.childPositions.filter (· ∉ keep)
    let A : Ctx.Context := σ.part keep Ctx.Side.lower m
    let B : Ctx.Context := σ.part rest Ctx.Side.upper n
    let C (q : ℕ) := B.cupLimit q q
    let color (q : ℕ) := if C q ≤ 2 then (0 : ℕ) else 1
    let support (c : ℕ) := B.childPositions.filter (fun q => color q = c)
    let group (c : ℕ) : Ctx.Context := { B with
      word := (List.range B.word.length).map (fun q => match B.letterAt q with
        | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
            else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
        | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
    let active (c : ℕ) := (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
    let I (c q : ℕ) := Finset.Icc ((group c).leftExt Ctx.Side.upper 0 q + 1)
      (B.a - 1 - (group c).rightExt Ctx.Side.upper 0 q)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let pairs (c : ℕ) := (active c).biUnion (fun q => Q (I c q))
    change ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
        A.bound + B.bound ≤ 12) ∨
      ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w
    by_cases hinter : ((pairs 0) ∩ (pairs 1)).card ≤ 1
    · left
      have hh := ctx_extreme_cut_six_twelve_of_pair_intersection_one σ hpositive
        Ctx.Side.lower Ctx.Side.upper hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen keep m n p high hp hm hk hhighmem hhigh
      change ((pairs 0) ∩ (pairs 1)).card ≤ 1 →
        (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
          A.bound + B.bound ≤ 12 at hh
      exact hh hinter
    · right
      have htwo : 1 < ((pairs 0) ∩ (pairs 1)).card := by omega
      obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp htwo
      exact ⟨z, hz, w, hw, hzw⟩
  · let rest := σ.childPositions.filter (· ∉ keep)
    let A : Ctx.Context := σ.part keep Ctx.Side.upper m
    let B : Ctx.Context := σ.part rest Ctx.Side.lower n
    let C (q : ℕ) := B.capLimit q q
    let color (q : ℕ) := if C q ≤ 2 then (0 : ℕ) else 1
    let support (c : ℕ) := B.childPositions.filter (fun q => color q = c)
    let group (c : ℕ) : Ctx.Context := { B with
      word := (List.range B.word.length).map (fun q => match B.letterAt q with
        | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
            else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
        | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
    let active (c : ℕ) := (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
    let I (c q : ℕ) := Finset.Icc ((group c).leftExt Ctx.Side.lower 0 q + 1)
      (B.u - 1 - (group c).rightExt Ctx.Side.lower 0 q)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let pairs (c : ℕ) := (active c).biUnion (fun q => Q (I c q))
    change ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
        A.bound + B.bound ≤ 12) ∨
      ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w
    by_cases hinter : ((pairs 0) ∩ (pairs 1)).card ≤ 1
    · left
      have hh := ctx_extreme_cut_six_twelve_of_pair_intersection_one σ hpositive
        Ctx.Side.upper Ctx.Side.lower hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen keep m n p high hp hm hk hhighmem hhigh
      change ((pairs 0) ∩ (pairs 1)).card ≤ 1 →
        (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
          A.bound + B.bound ≤ 12 at hh
      exact hh hinter
    · right
      have htwo : 1 < ((pairs 0) ∩ (pairs 1)).card := by omega
      obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp htwo
      exact ⟨z, hz, w, hw, hzw⟩
  · exact (hne rfl).elim

end ErdosSzekeres
