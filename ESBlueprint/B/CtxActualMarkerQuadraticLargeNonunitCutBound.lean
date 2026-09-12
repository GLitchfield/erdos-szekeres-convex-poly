import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxSmallGlobalAxisSaturatedTriangleBound
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Remove exact source depth: any selected actual chosen marker and arbitrary other history suffice, using the actual-marker companion theorem. Remove the retained-capacity-at-least-three and new-chosen-maximum-at-least-k-4 cut regime of the remaining one-level quadratic obstruction. Normalize the chosen part to global four and apply the actual-marker companion triangle; prove the top and next capacity-band polynomial budgets. Positive labels, any actual indexed chosen marker, arbitrary additional history, distinct axes and chosen global at most five. Opposite global at most k and k at least five. A retained child of chosen capacity at least three and a removed source child; arbitrary kept list, positive coupled maxima m+n=k-1, and m at least k-4. The sharper second conclusion assumes opposite global at most k-1. No source-maximum restriction, singleton-end geometry or recursive potential premise. This is a cut estimate. Lower new chosen maxima and retained capacities below three remain unresolved for the whole one-level quadratic potential. No exact-depth, youngest-marker or empty-history premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_quadratic_large_nonunit_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ) (hN : N∈σ.levels)
  (hside : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 5 ≤ σ.k)
  (keep : List ℕ) (m n p q : ℕ)
  (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m + n = σ.k - 1)
  (hnear : σ.k - 4 ≤ m)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep)
  (hcapacity : 3 ≤ (match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p)) :
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
  have hTriangle (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (s t : Side) (hne : s ≠ t)
      (hg : G ρ s ≤ 4) :
      ρ.bound ≤ (G ρ t).choose 2 := by
    let B := G ρ t
    let active := ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (ρ.leftExt t 0 p + 1) (B - 1 - ρ.rightExt t 0 p)
    let pairs := active.biUnion (fun p => ((I p).product (I p)).filter (fun z => z.1 ≤ z.2))
    let T := Finset.Icc 1 (B - 1)
    let triangle := (T.product T).filter (fun z => z.1 ≤ z.2)
    have hb := (ctx_small_global_axis_rank_pair_potential ρ hPos s t hne hg).2
    change ρ.bound ≤ pairs.card at hb
    have hInside (p : ℕ) : I p ⊆ T := by
      intro z hz
      have hh := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hSub : pairs ⊆ triangle := by
      intro z hz
      obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_filter.mp hz
      have hm := Finset.mem_product.mp hh.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hInside p hm.1, hInside p hm.2⟩, hh.2⟩
    have hCardPairs (T : Finset ℕ) :
        ((T.product T).filter (fun z => z.1 ≤ z.2)).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
      · intro z hz
        exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
      · intro p hp q hq he
        have hpl := (Finset.mem_filter.mp hp).2
        have hql := (Finset.mem_filter.mp hq).2
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · apply Prod.ext <;> omega
      · intro z hz
        induction z using Sym2.ind with
        | h a b =>
          obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
          by_cases hab : a ≤ b
          · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
              Sym2.eq_swap⟩
    have hTriangle : triangle.card = B.choose 2 := by
      change ((T.product T).filter (fun z => z.1 ≤ z.2)).card = B.choose 2
      rw [hCardPairs]
      by_cases hz : B = 0
      · norm_num [T, hz]
      · have hc : T.card + 1 = B := by
          simp only [T, Nat.card_Icc]
          omega
        rw [hc]
    exact hb.trans ((Finset.card_le_card hSub).trans_eq hTriangle)
  have hPosA := hPartPositive σ keep s m
  have hAlevel : 1 ∈ A.levels := by simp [A, part_levels]
  have hAx : q ∈ A.extPositions 1 := by
    rw [part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hq, by simp [hremoved]⟩
  have hAside : A.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hAx
  have hAmaximum : A.maximumAt 1 = m := part_maximumAt_one σ keep s m
  have hOn : 1 ∈ A.levelsOn s 0 := by simp [levelsOn, hAlevel, hAside]
  have hJoin : m ≤ A.joinExt s p p := by
    have hh := le_joinExt_of_mem_levelsOn hOn p p
    rw [hAmaximum] at hh
    omega
  have hmUpper : m ≤ σ.k - 4 := by
    cases s <;> change 3 ≤ min _ (σ.k - 1 - A.joinExt _ p p) at hcapacity
    all_goals omega
  have hmEq : m = σ.k - 4 := by omega
  have hCompanion := ctx_actual_marker_companion_maximum_bound σ hpositive s t hne N x
    hN hside hx hglobal keep m n p q hp hq hremoved
  have hBraw := (hCompanion.2.2 hcapacity).2
  have hbudget : σ.k - n - 1 + 1 = σ.k - 3 := by omega
  have hB : B.bound ≤ (σ.k - 3).choose 2 := by
    simpa only [hbudget] using hBraw
  let ν : Context := match s with
    | Side.lower => {A with u := min A.u (A.k - m), maxima := []}
    | Side.upper => {A with a := min A.a (A.k - m), maxima := []}
  have hνLetter (r : ℕ) : ν.letterAt r = A.letterAt r := by cases s <;> rfl
  have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
    intro r j v hj
    rw [hνLetter] at hj
    exact hPosA r j v hj
  have hνK : ν.k = σ.k := by cases s <;> rfl
  have hνG : G ν s ≤ 4 := by
    cases s <;> simp only [G, ν]
    all_goals exact (Nat.min_le_right _ _).trans (show σ.k - m ≤ 4 by omega)
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
  have hSat := ctx_small_global_axis_saturated_triangle_bound ν hνPos s t hne hνG
    (by change G ν t ≤ ν.k; rw [hνOpp, hνK]; exact hopposite)
    (by rw [hνK]; omega)
  have hA : A.bound ≤ (σ.k - 2).choose 2 + (σ.k - 1) := by
    exact hAν.trans (by simpa only [hνK] using hSat.2.1)
  have hDouble (a : ℕ) (ha : 1 ≤ a) : a * (a - 1) = a.choose 2 * 2 := by
    have hh := Nat.add_one_mul_choose_eq (a - 1) 1
    simpa only [Nat.sub_add_cancel ha, Nat.choose_one_right, Nat.reduceAdd] using hh
  have hTopIdentity (k : ℕ) (hk : 5 ≤ k) :
      (k - 2).choose 2 + (k - 1) + (k - 3).choose 2 =
        (k - 1) ^ 2 - 3 * (k - 1) + 4 := by
    let w := k - 3
    have hw : 2 ≤ w := by dsimp [w]; omega
    have h1 : k - 1 = w + 2 := by dsimp [w]; omega
    have h2 : k - 2 = w + 1 := by dsimp [w]; omega
    have h3 : k - 3 = w := rfl
    rw [h1, h2, h3]
    have hd1 := hDouble (w + 1) (by omega)
    have hd2 := hDouble w (by omega)
    have hd2' : w*w=w.choose 2*2+w := by
      calc
        w*w = w*((w-1)+1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]
        _ = w*(w-1)+w := by ring
        _ = w.choose 2*2+w := by rw [hd2]
    have hp : w - 1 + 1 = w := by omega
    have hcancel : w + 1 - 1 = w := by omega
    rw [hcancel] at hd1
    have hs : 3 * (w + 2) ≤ (w + 2) ^ 2 := by nlinarith
    have hr := Nat.sub_add_cancel hs
    nlinarith
  have hNextIdentity (k : ℕ) (hk : 5 ≤ k) :
      (k - 1).choose 2 + (k - 3).choose 2 =
        (k - 2) ^ 2 - (k - 2) + 1 := by
    let w := k - 3
    have hw : 2 ≤ w := by dsimp [w]; omega
    have h1 : k - 1 = w + 2 := by dsimp [w]; omega
    have h2 : k - 2 = w + 1 := by dsimp [w]; omega
    have h3 : k - 3 = w := rfl
    rw [h1, h2, h3]
    have hd1 := hDouble (w + 2) (by omega)
    have hd2 := hDouble w (by omega)
    have hd2' : w*w=w.choose 2*2+w := by
      calc
        w*w = w*((w-1)+1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]
        _ = w*(w-1)+w := by ring
        _ = w.choose 2*2+w := by rw [hd2]
    have hp : w - 1 + 1 = w := by omega
    have hcancel : w + 2 - 1 = w + 1 := by omega
    rw [hcancel] at hd1
    have hs : w + 1 ≤ (w + 1) ^ 2 := by nlinarith
    have hr := Nat.sub_add_cancel hs
    nlinarith
  constructor
  · exact (Nat.add_le_add hA hB).trans_eq (hTopIdentity σ.k hk)
  · intro hnext
    have hOrdinary := hTriangle ν hνPos s t hne hνG
    change ν.bound ≤ (G ν t).choose 2 at hOrdinary
    rw [hνOpp] at hOrdinary
    have hA' : A.bound ≤ (σ.k - 1).choose 2 :=
      hAν.trans (hOrdinary.trans (Nat.choose_le_choose 2 hnext))
    exact (Nat.add_le_add hA' hB).trans_eq (hNextIdentity σ.k hk)


end ErdosSzekeres
