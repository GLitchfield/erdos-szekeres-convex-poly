import ESBlueprint.B.CtxNonmonotoneNewMarkerLowMaximumCutBound
import ESBlueprint.B.CtxTwoActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- Cover every positive nonmonotone new-marker cut with two actual chosen source markers and positive opposite maximum. If m+3<=k, consume the checked low-maximum cut theorem. Otherwise coupling and n>=1 force the extreme values m+2=k and n=1. The chosen part is then at most one by the checked large-sibling-maximum theorem, while the two-actual-marker companion theorem bounds the opposite part by choose(k-1,2)+k-3. Their sum fits the top quadratic budget for k>=6, with doubled slack (k-3)(k-6), and fits the next budget for k>=7, with doubled slack k^2-9k+16. Thus only the k=6 extreme remains outside the next-band conclusion. Positive labels, retained and removed child witnesses, arbitrary kept lists, two ordered actual chosen levels, nonmonotone new-marker geometry, distinct axes, chosen global at most five, opposite global at most k, k at least six and cut coupling are explicit. No active-child assumption beyond the stated retained witness is introduced. Exact pre-draft es searches for 'nonmonotone new marker cut all maxima except k six extreme' and 'large sibling maximum bound one companion two actual markers cut' returned no results.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_new_marker_cut_bound_except_six_extreme (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (keep : List ℕ) (s t : Ctx.Side) (hne : s ≠ t) (m n p q N M x y : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hqnot : q ∉ keep)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (q < x ∧ y < x) ∨ (x < q ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 6 ≤ σ.k) (hcoupling : m + n = σ.k - 1) (hn : 1 ≤ n) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤
    (σ.k - 1)^2 - 3 * (σ.k - 1) + 4) ∧
    A.bound + B.bound ≤ (σ.k - 1)^2 - 3 * (σ.k - 1) + 4 ∧
    (((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1) ∧
      (m + 3 ≤ σ.k ∨ 7 ≤ σ.k) →
      (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤
        (σ.k - 2)^2 - (σ.k - 2) + 1) ∧
      A.bound + B.bound ≤ (σ.k - 2)^2 - (σ.k - 2) + 1) := by
  set_option maxHeartbeats 8000000 in
    let A := σ.part keep s m
    let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
    by_cases hlow : m + 3 ≤ σ.k
    · have hLow := ctx_nonmonotone_new_marker_low_maximum_cut_bound σ hpositive
        keep s t hne m n p q N M x y hp hq hqnot hN hM hNM hNs hMs hx hy
        hgeometry (by cases s <;> exact hglobal) (by cases t <;> exact hopposite)
        hk hcoupling hlow
      exact ⟨hLow.1, hLow.2.1, fun hnext => hLow.2.2 hnext.1⟩
    · have hm : m + 2 = σ.k := by omega
      have hnOne : n = 1 := by omega
      have hPosA : ∀ r j v, A.letterAt r = Ctx.Letter.ext j v → 1 ≤ j :=
        ctx_part_positive_letters σ keep s m
      have hAOne : 1 ∈ A.levels := by
        simp only [A, Ctx.Context.part_levels, List.mem_cons, true_or]
      have hlarge : σ.k - 2 ≤ m := by omega
      have hA := ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAOne
        (by simpa only [A, Ctx.Context.part_maximumAt_one] using hlarge)
      have hCompanion := ctx_two_actual_marker_companion_maximum_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy
        (by cases s <;> exact hglobal) keep m n p q hp hq hqnot
      have hbudget : σ.k - n - 1 = σ.k - 2 := by omega
      have hBFuel (g : ℕ) : Ctx.Context.boundFuel g B ≤
          (σ.k - 2 + 1).choose 2 + (σ.k - 2) - 1 := by
        simpa only [B, hbudget] using hCompanion.1 g
      have hBBound : B.bound ≤ (σ.k - 2 + 1).choose 2 + (σ.k - 2) - 1 := by
        simpa only [B, hbudget] using hCompanion.2
      have hTwoChoose (r : ℕ) : 2 * (r + 1).choose 2 = r * r + r := by
        induction r with
        | zero => norm_num
        | succ r ih =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          nlinarith
      have hTopNumeric (k : ℕ) (hk6 : 6 ≤ k) :
          1 + ((k - 2 + 1).choose 2 + (k - 2) - 1) ≤
            (k - 1) ^ 2 - 3 * (k - 1) + 4 := by
        let z := k - 6
        have hz : 0 ≤ z := Nat.zero_le z
        have h2 : k - 2 = z + 4 := by dsimp [z]; omega
        have h1 : k - 1 = z + 5 := by dsimp [z]; omega
        rw [h2, h1]
        have hc := hTwoChoose (z + 4)
        have hLeftPos : 1 ≤ (z + 4 + 1).choose 2 + (z + 4) := by omega
        have hLeftCancel := Nat.sub_add_cancel hLeftPos
        have hRightSub : 3 * (z + 5) ≤ (z + 5) ^ 2 := by
          set_option maxHeartbeats 2000000 in
            nlinarith only [hz]
        have hRightCancel := Nat.sub_add_cancel hRightSub
        set_option maxHeartbeats 2000000 in
          nlinarith only [hz, hc, hLeftCancel, hRightCancel]
      have hNextNumeric (k : ℕ) (hk7 : 7 ≤ k) :
          1 + ((k - 2 + 1).choose 2 + (k - 2) - 1) ≤
            (k - 2) ^ 2 - (k - 2) + 1 := by
        let z := k - 7
        have hz : 0 ≤ z := Nat.zero_le z
        have h2 : k - 2 = z + 5 := by dsimp [z]; omega
        rw [h2]
        have hc := hTwoChoose (z + 5)
        have hLeftPos : 1 ≤ (z + 5 + 1).choose 2 + (z + 5) := by omega
        have hLeftCancel := Nat.sub_add_cancel hLeftPos
        have hRightSub : z + 5 ≤ (z + 5) ^ 2 := by
          set_option maxHeartbeats 2000000 in
            nlinarith only [hz]
        have hRightCancel := Nat.sub_add_cancel hRightSub
        set_option maxHeartbeats 2000000 in
          nlinarith only [hz, hc, hLeftCancel, hRightCancel]
      refine ⟨?_, ?_, ?_⟩
      · intro f g
        exact (Nat.add_le_add (hA.1 f) (hBFuel g)).trans (hTopNumeric σ.k hk)
      · exact (Nat.add_le_add hA.2 hBBound).trans (hTopNumeric σ.k hk)
      · rintro ⟨_, hrange⟩
        have hk7 : 7 ≤ σ.k := hrange.resolve_left hlow
        exact ⟨fun f g =>
            (Nat.add_le_add (hA.1 f) (hBFuel g)).trans (hNextNumeric σ.k hk7),
          (Nat.add_le_add hA.2 hBBound).trans (hNextNumeric σ.k hk7)⟩


end ErdosSzekeres
