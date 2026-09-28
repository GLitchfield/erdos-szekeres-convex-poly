import ESBlueprint.B.CtxSingleLevelSaturatedLinearBound
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential
import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Bound every positive context with chosen global at most four and opposite global at most k by choose(k-2,2)+k-1 for k>=4. A local history truncation transports the checked saturated-linear marker estimate to arbitrary depth; sibling maxima give the complementary triangular charge. The three possible maximum ranges are paid by exact Pascal identities.
Positive physical external labels, distinct chosen/opposite axes, chosen global at most four, opposite global at most k, and k at least four. Arbitrary indexed histories, maxima, inactive children, positive unindexed barriers and child pattern; no actual-marker or recursive-potential premise.

The public statement also bounds the full cut for every arbitrary complementary kept list with retained and removed child witnesses and positive new maxima summing to k-1. No interval-convexity premise is used. Additional search `es search "global four saturated triangular budget arbitrary complementary kept subsets positive coupled maxima"` returned no hits; record `runs/2026-09-10-active-lean-research/saturated-global-four-arbitrary-cut-search.json`.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_axis_saturated_triangle_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 4 ≤ σ.k) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (σ.k - 2).choose 2 + (σ.k - 1)) ∧
    σ.bound ≤ (σ.k - 2).choose 2 + (σ.k - 1) ∧
    (∀ keep : List ℕ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m+n=σ.k-1 →
      ∀ p q : ℕ, p ∈ σ.childPositions → p ∈ keep → q ∈ σ.childPositions → q ∉ keep →
        (σ.part keep s m).bound +
          (σ.part (σ.childPositions.filter (· ∉ keep)) t n).bound ≤
            (σ.k - 2).choose 2 + (σ.k - 1)) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let K := (σ.k - 2).choose 2 + (σ.k - 1)
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x j v, (ρ.part keep t m).letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx; omega
  have hFuelFull (ρ : Context) (f : ℕ) : boundFuel f ρ ≤ ρ.bound := by
    by_cases hf : ρ.childPositions.length + 1 ≤ f
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : f ≤ ρ.childPositions.length + 1) ρ
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
  have hSatMarker (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (s t : Side) (hne : s ≠ t) (x : ℕ)
      (hOne : 1 ∈ ρ.levels) (hSide : ρ.sideAt 1 = s) (hx : x ∈ ρ.extPositions 1)
      (hg : G ρ s ≤ 4)
      (ho : (G ρ t) ≤ ρ.k)
      (hk : 4 ≤ ρ.k) : ρ.bound ≤ 2 * ρ.k - 4 := by
    let τ : Context := { ρ with maxima := ρ.maxima.take 1 }
    have hD : 1 ≤ ρ.maxima.length := by
      have hh := hOne
      simp only [levels, List.mem_map, List.mem_range] at hh
      obtain ⟨i, hi, he⟩ := hh
      omega
    have hτDepth : τ.maxima.length = 1 := by
      simp only [τ, List.length_take]
      omega
    have hToτ : ρ.bound ≤ τ.bound := by
      by_cases hd : ρ.maxima.length = 1
      · have ht : ρ.maxima.take 1 = ρ.maxima := List.take_of_length_le (by omega)
        simpa only [τ, ht] using (le_rfl : ρ.bound ≤ ρ.bound)
      have hTwo : 2 ∈ ρ.levels := by
        apply List.mem_map.mpr
        exact ⟨1, List.mem_range.mpr (by omega), rfl⟩
      have hn := (ctx_sibling_maximum_upper_normalize ρ 2 hTwo).2.2
      cases hs : ρ.sideAt 2 with
      | lower =>
        let ν : Context := { ρ with u := min ρ.u (ρ.k - ρ.maximumAt 2), maxima := ρ.maxima.take 1 }
        have hρν : ρ.bound ≤ ν.bound := by
          simpa only [hs, Nat.reduceSub] using hn
        have hντ := ctx_bound_mono_of_marker_inclusion ν τ hPos hPos
          (le_rfl : ρ.a ≤ ρ.a) (Nat.min_le_left _ _) rfl rfl
          (fun _ => Iff.rfl) rfl
          (fun _ _ => ⟨rfl, fun _ hp => hp, le_rfl⟩)
        exact hρν.trans hντ.2.2
      | upper =>
        let ν : Context := { ρ with a := min ρ.a (ρ.k - ρ.maximumAt 2), maxima := ρ.maxima.take 1 }
        have hρν : ρ.bound ≤ ν.bound := by
          simpa only [hs, Nat.reduceSub] using hn
        have hντ := ctx_bound_mono_of_marker_inclusion ν τ hPos hPos
          (Nat.min_le_left _ _) (le_rfl : ρ.u ≤ ρ.u) rfl rfl
          (fun _ => Iff.rfl) rfl
          (fun _ _ => ⟨rfl, fun _ hp => hp, le_rfl⟩)
        exact hρν.trans hντ.2.2
    have hh := ctx_single_level_saturated_linear_bound τ hPos hτDepth s t hne x
      hSide hx hg ho hk
    exact hToτ.trans hh.2
  have hCompanionTriangle (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (s t : Side) (hne : s ≠ t)
      (hg : G ρ s ≤ 4)
      (N : ℕ) (hN : N ∈ ρ.levels) (hSide : ρ.sideAt N = t) :
      ρ.bound ≤ (min (G ρ t)
        (ρ.k - ρ.maximumAt N)).choose 2 := by
    have hn := (ctx_sibling_maximum_upper_normalize ρ N hN).2.2
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · let ν : Context := { ρ with a := min ρ.a (ρ.k - ρ.maximumAt N), maxima := ρ.maxima.take (N-1) }
      have hρν : ρ.bound ≤ ν.bound := by simpa only [hSide] using hn
      have hh := hTriangle ν hPos Side.lower Side.upper (by decide) hg
      exact hρν.trans hh
    · let ν : Context := { ρ with u := min ρ.u (ρ.k - ρ.maximumAt N), maxima := ρ.maxima.take (N-1) }
      have hρν : ρ.bound ≤ ν.bound := by simpa only [hSide] using hn
      have hh := hTriangle ν hPos Side.upper Side.lower (by decide) hg
      exact hρν.trans hh
    · exact False.elim (hne rfl)
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hSaturatedBaseEdge (k : ℕ) (hk : 4 ≤ k) :
      baseOf 3 (k - 1) k = (k - 2).choose 2 + (k - 1) := by
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega)]
    rw [show k - 1 + 1 = k by omega]
    rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
    have hw : decomposableBinomialWindow k (3 + 1) k =
        1 + (k - 2) + (k - 2).choose 2 := by
      norm_num [decomposableBinomialWindow, Finset.sum_Icc_succ_top]
    rw [hw]
    omega
  have hSaturatedBase (ρ : Context) (s : Side)
      (hg : G ρ s ≤ 4)
      (hk : 4 ≤ ρ.k) : ρ.base ≤ (ρ.k - 2).choose 2 + (ρ.k - 1) := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤
        (ρ.k - 2).choose 2 + (ρ.k - 1)
      have hc : (match s with | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p) ≤ 3 := by
        cases s <;> simp only [G, cupLimit, capLimit] at hg ⊢ <;> omega
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      rw [← hSaturatedBaseEdge ρ.k hk]
      cases s
      · exact baseOf_mono hc hcapk
      · rw [hBaseSwap _ _ _ hcupk hcapk]
        exact baseOf_mono hc hcupk
  have hBase : σ.base ≤ K := hSaturatedBase σ s hglobal hk
  have hCut (fuel : ℕ) (keep : List ℕ) (m n p q : ℕ)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m + n = σ.k - 1)
      (hp : p ∈ σ.childPositions) (hpk : p ∈ keep)
      (hq : q ∈ σ.childPositions) (hqk : q ∉ keep) :
      boundFuel fuel (σ.part keep s m) +
        boundFuel fuel (σ.part (σ.childPositions.filter (· ∉ keep)) t n) ≤ K := by
    let rest := σ.childPositions.filter (· ∉ keep)
    let A := σ.part keep s m
    let B := σ.part rest t n
    have hPosA := hPositivePart σ keep s m
    have hPosB := hPositivePart σ rest t n
    have hAlevel : 1 ∈ A.levels := by simp [A, part_levels]
    have hBlevel : 1 ∈ B.levels := by simp [B, part_levels]
    have hAmaximum : A.maximumAt 1 = m := part_maximumAt_one σ keep s m
    have hBmaximum : B.maximumAt 1 = n := part_maximumAt_one σ rest t n
    have hAx : q ∈ A.extPositions 1 := by
      simp [A, part_extPositions_one hpositive keep s m, hq, hqk]
    have hBx : p ∈ B.extPositions 1 := by
      change p ∈ (σ.part rest t n).extPositions 1
      rw [part_extPositions_one hpositive rest t n]
      exact List.mem_filter.mpr ⟨hp, by simp [rest, hpk]⟩
    have hAside : A.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hAx
    have hBside : B.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hBx
    have hAg : G A s ≤ 4 := by cases s <;> exact hglobal
    have hBg : G B s ≤ 4 := by cases s <;> exact hglobal
    have hBraw := hCompanionTriangle B hPosB s t hne hBg 1 hBlevel hBside
    change B.bound ≤ (min (G B t) (σ.k - B.maximumAt 1)).choose 2 at hBraw
    rw [hBmaximum] at hBraw
    have hBcap : min (G B t) (σ.k - n) ≤ m + 1 := by
      have hh := Nat.min_le_right (G B t) (σ.k - n)
      omega
    have hB : B.bound ≤ (m + 1).choose 2 := hBraw.trans (Nat.choose_le_choose 2 hBcap)
    have hLift : A.bound + B.bound ≤ K → boundFuel fuel A + boundFuel fuel B ≤ K :=
      fun h => (Nat.add_le_add (hFuelFull A fuel) (hFuelFull B fuel)).trans h
    apply hLift
    by_cases hlarge : σ.k - 2 ≤ m
    · have hA := (ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAlevel
        (by change σ.k - 2 ≤ A.maximumAt 1; rw [hAmaximum]; exact hlarge)).2
      have hmEq : m + 1 = σ.k - 1 := by omega
      rw [hmEq] at hB
      have hPred : σ.k - 2 + 1 = σ.k - 1 := by omega
      have hPascal : (σ.k - 1).choose 2 = (σ.k - 2).choose 2 + (σ.k - 2) := by
        simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, hPred, Nat.add_comm]
          using Nat.choose_succ_succ (σ.k - 2) 1
      dsimp only [K]
      omega
    have hmle : m ≤ σ.k - 3 := by omega
    by_cases hnear : σ.k - 3 ≤ m
    · let ν : Context := match s with
        | Side.lower => { A with u := min A.u (A.k - m), maxima := [] }
        | Side.upper => { A with a := min A.a (A.k - m), maxima := [] }
      have hνLetter (r : ℕ) : ν.letterAt r = A.letterAt r := by cases s <;> rfl
      have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
        intro r j v hj
        rw [hνLetter] at hj
        exact hPosA r j v hj
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
      have hsmall := ctx_small_global_axis_rank_region_potential ν hνPos s t hne hνG
      have hνbound : ν.bound ≤ G ν t - 1 := by
        cases t <;> exact hsmall.2.1.trans hsmall.2.2.1
      rw [hνOpp] at hνbound
      have hA : A.bound ≤ σ.k - 1 := hAν.trans (hνbound.trans (by
        change G σ t ≤ σ.k at hopposite
        omega))
      have hmEq : m + 1 = σ.k - 2 := by omega
      rw [hmEq] at hB
      dsimp only [K]
      omega
    have hA : A.bound ≤ 2 * σ.k - 4 := hSatMarker A hPosA s t hne q
      hAlevel hAside hAx hAg (by cases t <;> exact hopposite) hk
    have hB' : B.bound ≤ (σ.k - 3).choose 2 :=
      hB.trans (Nat.choose_le_choose 2 (by omega))
    have hPred : σ.k - 3 + 1 = σ.k - 2 := by omega
    have hPascal : (σ.k - 2).choose 2 = (σ.k - 3).choose 2 + (σ.k - 3) := by
      simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, hPred, Nat.add_comm]
        using Nat.choose_succ_succ (σ.k - 3) 1
    dsimp only [K]
    omega
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ K := by
    intro fuel
    cases fuel with
    | zero => exact Nat.zero_le _
    | succ fuel =>
      rw [boundFuel]
      split
      · exact hBase
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, hd, hz⟩ := hz
        have hd' := List.mem_range.mp hd
        obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hkeep
        obtain ⟨p, hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ σ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup σ).subperm h).length_le
          omega
        obtain ⟨q, hq, hqk⟩ := hremoved
        let rest := σ.childPositions.filter (· ∉ keep)
        have hforward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            boundFuel fuel (σ.part keep s a) + boundFuel fuel (σ.part rest t b) ≤ K :=
          hCut fuel keep a b p q ha hb hab hp hpk hq hqk
        have hdouble (v : Side) (m : ℕ) :
            σ.part (σ.childPositions.filter (· ∉ rest)) v m = σ.part keep v m := by
          apply part_congr
          intro r hr
          simp only [rest, List.mem_filter, decide_eq_true_eq, hr, true_and, not_not]
        have hbackward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            boundFuel fuel (σ.part rest s a) + boundFuel fuel (σ.part keep t b) ≤ K := by
          have hh := hCut fuel rest a b q p ha hb hab
            hq (by simp [rest, hq, hqk]) hp (by simp [rest, hpk])
          rw [hdouble] at hh
          exact hh
        have hboth (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            (boundFuel fuel (σ.part keep Side.lower a) +
              boundFuel fuel (σ.part rest Side.upper b) ≤ K) ∧
            (boundFuel fuel (σ.part keep Side.upper b) +
              boundFuel fuel (σ.part rest Side.lower a) ≤ K) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b ha hb hab,
              by simpa only [Nat.add_comm] using hbackward a b ha hb hab⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a hb ha (by omega),
              hforward b a hb ha (by omega)⟩
          · exact False.elim (hne rfl)
        have hall := hboth (d+1) (σ.k-1-(d+1)) (by omega) (by omega) (by omega)
        rcases hz with rfl | rfl
        · exact hall.1
        · exact hall.2
  refine ⟨hFuel, hFuel _, ?_⟩
  intro keep m n hm hn hmn p q hp hpk hq hqk
  have hFullPart (ks : List ℕ) (v : Side) (M : ℕ) :
      boundFuel (σ.childPositions.length+1) (σ.part ks v M) = (σ.part ks v M).bound := by
    apply boundFuel_eq_bound
    rw [part_childPositions]
    exact Nat.add_le_add_right (List.length_filter_le _ _) 1
  have hc := hCut (σ.childPositions.length+1) keep m n p q hm hn hmn hp hpk hq hqk
  simpa only [hFullPart] using hc

end ErdosSzekeres
