import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxSmallMaximaActiveCapacityTwoLinearPotential
import ESBlueprint.B.CtxSingleLevelSaturatedLinearBound
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- For a positive exact-depth-one source with an actual chosen marker, chosen global at most five, opposite global between two and k, and k at least six, prove both critical quadratic cut budgets when the new chosen maximum is at most k-5 and all active chosen-part capacities are at most two. The old source maximum is unrestricted: a small old maximum permits the thin linear potential, while a large one can be normalized and leaves an actual new marker in a global-four depth-one context. The opposite companion square then pays the top budget (k-1)^2-3(k-1)+4 and next budget (k-2)^2-(k-2)+1. The kept list is arbitrary; new maxima are positive and coupled. There is no recursive premise. Cuts with a capacity-three retained witness remain separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_level_quadratic_small_capacity_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (hdepth : σ.maxima.length = 1)
  (s t : Ctx.Side) (hne : s ≠ t) (x : ℕ)
  (hside : σ.sideAt 1 = s) (hx : x ∈ σ.extPositions 1)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a))
  (hk : 6 ≤ σ.k)
  (keep : List ℕ) (m n p q : ℕ)
  (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m + n = σ.k - 1)
  (hlow : m ≤ σ.k - 5)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep)
  (hsmall : ∀ r ∈ (σ.part keep s m).childPositions,
    0 < (σ.part keep s m).cupLimit r r → 0 < (σ.part keep s m).capLimit r r →
    (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit r r
      | Ctx.Side.upper => (σ.part keep s m).capLimit r r) ≤ 2) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  A.bound + B.bound ≤ (σ.k - 1) ^ 2 - 3 * (σ.k - 1) + 4 ∧
    ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1 →
      A.bound + B.bound ≤ (σ.k - 2) ^ 2 - (σ.k - 2) + 1) := by
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
  have hApartG (v : Side) : G A v = G σ v := by cases v <;> rfl
  have hAg : G A s ≤ 5 := by rw [hApartG]; exact hglobal
  have hAlevels : A.levels = [1, 2] := by
    change (σ.part keep s m).levels = [1, 2]
    rw [part_levels]
    simp [levels, hdepth]
  have hAlevel : 1 ∈ A.levels := by simp [hAlevels]
  have hAoldLevel : 2 ∈ A.levels := by simp [hAlevels]
  have hAx : q ∈ A.extPositions 1 := by
    rw [part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hq, by simp [hremoved]⟩
  have hAside : A.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hAx
  have hOldSide : A.sideAt 2 = s :=
    (part_sideAt_succ σ keep s m (show 1 ≤ 1 by decide)).trans hside
  have hAmaximum : A.maximumAt 1 = m := part_maximumAt_one σ keep s m
  have hOldMax : A.maximumAt 2 = σ.maximumAt 1 :=
    part_maximumAt_succ σ keep s m (show 1 ≤ 1 by decide)
  have hCompanion := ctx_actual_marker_companion_maximum_bound σ hpositive s t hne 1 x
    (by simp [levels,hdepth]) hside hx hglobal keep m n p q hp hq hremoved
  have hBraw := hCompanion.2.1
  have hbudget : σ.k - n - 1 = m := by omega
  have hB : B.bound ≤ (σ.k - 5) ^ 2 := by
    have hh : B.bound ≤ m ^ 2 := by simpa only [hbudget] using hBraw
    exact hh.trans (Nat.pow_le_pow_left hlow 2)
  have hAbudgets : A.bound ≤ 3 * (σ.k - 1) - 2 ∧
      (G σ t ≤ σ.k - 1 → A.bound ≤ 3 * (σ.k - 2) - 2) := by
    by_cases hold : σ.maximumAt 1 ≤ σ.k - 5
    · have hmax : ∀ j ∈ A.levelsOn s 0, A.maximumAt j ≤ A.k - 5 := by
        intro j hj
        have hj' := (List.mem_filter.mp hj).1
        have he : j = 1 ∨ j = 2 := by simpa [hAlevels] using hj'
        rcases he with rfl | rfl
        · rw [hAmaximum]; exact hlow
        · rw [hOldMax]; exact hold
      have hw : 1 ≤ G A t - 1 := by rw [hApartG]; change 2 ≤ G σ t at hwidth; omega
      have hthin := ctx_small_maxima_active_capacity_two_linear_potential A hPosA s t hne hAg
        (by change 5 ≤ σ.k; omega) hmax hsmall hw
      have hb := hthin.2
      change A.bound ≤ 3 * (G A t - 1) - 2 at hb
      rw [hApartG] at hb
      change G σ t ≤ σ.k at hopposite
      exact ⟨by omega, fun hnext => by omega⟩
    · let ν : Context := match s with
        | Side.lower => {A with u := min A.u (A.k - σ.maximumAt 1), maxima := A.maxima.take 1}
        | Side.upper => {A with a := min A.a (A.k - σ.maximumAt 1), maxima := A.maxima.take 1}
      have hνLetter (r : ℕ) : ν.letterAt r = A.letterAt r := by cases s <;> rfl
      have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
        intro r j v hj
        rw [hνLetter] at hj
        exact hPosA r j v hj
      have hνK : ν.k = σ.k := by cases s <;> rfl
      have hνDepth : ν.maxima.length = 1 := by cases s <;> simp [ν, A, part, hdepth]
      have hνSide : ν.sideAt 1 = s := by cases s <;> exact hAside
      have hνExt : q ∈ ν.extPositions 1 := by cases s <;> exact hAx
      have hνG : G ν s ≤ 4 := by
        cases s <;> simp only [G, ν]
        all_goals exact (Nat.min_le_right _ _).trans (show σ.k - σ.maximumAt 1 ≤ 4 by omega)
      have hνOpp : G ν t = G σ t := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · rfl
        · rfl
        · exact False.elim (hne rfl)
      have hnorm := ctx_sibling_maximum_upper_normalize A 2 hAoldLevel
      have hAν : A.bound ≤ ν.bound := by
        cases s <;> simpa only [ν, hOldSide, hOldMax, Nat.reduceSub] using hnorm.2.2
      have hlinear := ctx_single_level_saturated_linear_bound ν hνPos hνDepth s t hne q
        hνSide hνExt hνG
        (by change G ν t ≤ ν.k; rw [hνOpp, hνK]; exact hopposite)
        (by rw [hνK]; omega)
      have hb : A.bound ≤ 2 * σ.k - 4 := hAν.trans (by simpa only [hνK] using hlinear.2)
      exact ⟨by omega, fun _ => by omega⟩
  have hNumeric (k : ℕ) (hk : 6 ≤ k) :
      3 * (k - 1) - 2 + (k - 5) ^ 2 ≤ (k - 1) ^ 2 - 3 * (k - 1) + 4 ∧
      3 * (k - 2) - 2 + (k - 5) ^ 2 ≤ (k - 2) ^ 2 - (k - 2) + 1 := by
    let w := k - 5
    have hw : 1 ≤ w := by dsimp [w]; omega
    have h1 : k - 1 = w + 4 := by dsimp [w]; omega
    have h2 : k - 2 = w + 3 := by dsimp [w]; omega
    have h5 : k - 5 = w := rfl
    rw [h1, h2, h5]
    have htop : 3 * (w + 4) - 2 = 3 * w + 10 := by omega
    have hnext : 3 * (w + 3) - 2 = 3 * w + 7 := by omega
    rw [htop, hnext]
    have hsTop : 3 * (w + 4) ≤ (w + 4) ^ 2 := by nlinarith
    have hrTop := Nat.sub_add_cancel hsTop
    have hsNext : w + 3 ≤ (w + 3) ^ 2 := by nlinarith
    have hrNext := Nat.sub_add_cancel hsNext
    constructor <;> nlinarith
  exact ⟨(Nat.add_le_add hAbudgets.1 hB).trans (hNumeric σ.k hk).1,
    fun hnext => (Nat.add_le_add (hAbudgets.2 hnext) hB).trans (hNumeric σ.k hk).2⟩


end ErdosSzekeres
