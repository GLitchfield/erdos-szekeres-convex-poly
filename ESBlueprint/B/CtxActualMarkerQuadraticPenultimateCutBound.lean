import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Remove exact source depth: any selected actual chosen marker and arbitrary other history suffice, using the actual-marker companion theorem. Close the penultimate chosen-maximum case in the proposed saturated one-level quadratic potential. The chosen part normalizes to global three and is linear in opposite width; the companion square bound gives (k-3)^2. Their sum exactly meets the top and next quadratic budgets, with no retained-capacity or cut-geometry assumption. Positive labels, any actual indexed chosen marker, arbitrary additional history, distinct axes and chosen global at most five. Opposite global at most k and k at least five; arbitrary kept list with a retained source child and a removed source child. Coupled new maxima m+n=k-1 with m+3=k (hence n=2). The second bound additionally requires opposite global at most k-1. Arbitrary old sibling maximum, repeated actual markers and positive unindexed barriers; no retained-capacity, convexity, singleton-end, or recursive-potential premise. The maxima k-4 and k-2 cases are separate. No exact-depth, youngest-marker or empty-history premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_quadratic_penultimate_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r=Ctx.Letter.ext j v → 1≤j)
  (s t : Ctx.Side) (hne : s≠t) (N x : ℕ) (hN : N∈σ.levels)
  (hside : σ.sideAt N=s) (hx : x∈σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤σ.k)
  (hk : 5≤σ.k)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p∈(σ.part keep s m).childPositions)
  (hq : q∈σ.childPositions) (hremoved : q∉keep)
  (hcoupling : m+n=σ.k-1) (hmaximum : m+3=σ.k) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (·∉keep)) t n
  A.bound+B.bound≤(σ.k-1)^2-3*(σ.k-1)+4 ∧
    ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤σ.k-1 →
      A.bound+B.bound≤(σ.k-2)^2-(σ.k-2)+1) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  change A.bound + B.bound ≤ (σ.k - 1) ^ 2 - 3 * (σ.k - 1) + 4 ∧
    (G σ t ≤ σ.k - 1 → A.bound + B.bound ≤ (σ.k - 2) ^ 2 - (σ.k - 2) + 1)
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hPosA := hPartPositive σ keep s m
  have hAlevel : 1∈A.levels := by simp [A,part_levels]
  have hAx : q∈A.extPositions 1 := by
    rw [part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hq,by simp [hremoved]⟩
  have hAside : A.sideAt 1=s := part_sideAt_one_of_mem hpositive keep s m hAx
  have hAmaximum : A.maximumAt 1=m := part_maximumAt_one σ keep s m
  have hCompanion := ctx_actual_marker_companion_maximum_bound σ hpositive s t hne N x
    hN hside hx hglobal keep m n p q hp hq hremoved
  have hbudget : σ.k-n-1=m := by omega
  have hmEq : m=σ.k-3 := by omega
  have hB : B.bound≤(σ.k-3)^2 := by
    simpa only [hbudget,hmEq] using hCompanion.2.1
  let ν : Context := match s with
    | Side.lower => {A with u := min A.u (A.k - m), maxima := []}
    | Side.upper => {A with a := min A.a (A.k - m), maxima := []}
  have hνLetter (r : ℕ) : ν.letterAt r = A.letterAt r := by cases s <;> rfl
  have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
    intro r j v hj
    rw [hνLetter] at hj
    exact hPosA r j v hj
  have hνK : ν.k = σ.k := by cases s <;> rfl
  have hνG : G ν s ≤ 3 := by
    cases s <;> simp only [G, ν]
    all_goals exact (Nat.min_le_right _ _).trans (show σ.k - m ≤ 3 by omega)
  have hνOpp : G ν t = G σ t := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · rfl
    · rfl
    · exact False.elim (hne rfl)
  have hnorm := ctx_sibling_maximum_upper_normalize A 1 hAlevel
  have hAν : A.bound ≤ ν.bound := by
    cases s <;>
      simpa only [ν, hAside, hAmaximum, Nat.sub_self, List.take_zero] using hnorm.2.2
  have hLinear := ctx_small_global_axis_rank_region_potential ν hνPos s t hne hνG
  have hνBound : ν.bound≤G ν t-1 := by
    cases t <;> exact hLinear.2.1.trans hLinear.2.2.1
  rw [hνOpp] at hνBound
  have hA : A.bound≤G σ t-1 := hAν.trans hνBound
  have hNumeric (k : ℕ) (hk : 5≤k) :
      (k-1)+(k-3)^2=(k-1)^2-3*(k-1)+4 ∧
      (k-2)+(k-3)^2=(k-2)^2-(k-2)+1 := by
    let w := k-3
    have hw : 2≤w := by dsimp [w]; omega
    have h1 : k-1=w+2 := by dsimp [w]; omega
    have h2 : k-2=w+1 := by dsimp [w]; omega
    rw [h1,h2,show k-3=w by rfl]
    have hsTop : 3*(w+2)≤(w+2)^2 := by nlinarith
    have hrTop := Nat.sub_add_cancel hsTop
    have hsNext : w+1≤(w+1)^2 := by nlinarith
    have hrNext := Nat.sub_add_cancel hsNext
    constructor <;> nlinarith
  constructor
  · have hA' : A.bound≤σ.k-1 := hA.trans (by change G σ t≤σ.k at hopposite; omega)
    exact (Nat.add_le_add hA' hB).trans_eq (hNumeric σ.k hk).1
  · intro hnext
    have hA' : A.bound≤σ.k-2 := hA.trans (by omega)
    exact (Nat.add_le_add hA' hB).trans_eq (hNumeric σ.k hk).2


end ErdosSzekeres
