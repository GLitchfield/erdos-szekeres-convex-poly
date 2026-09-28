import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxTwoActualMarkerSharpPotentialArbitraryHistory
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Use the checked sharp arbitrary-history two-marker potential on the chosen part and the companion triangle on the opposite part. For chosen maximum m<=k-6, the resulting sum is below the next-band quadratic target by at least k-6. No stronger saturated two-marker potential is assumed. Small opposite widths are handled locally by the checked small-global rank-region bound. Positive labels, distinct axes, any actual indexed chosen marker and chosen global at most five; arbitrary additional history and repeated markers. Opposite global at most k-1. Positive chosen maximum m<=k-6 and coupling m+n=k-1 imply k>=7 and n>=5. No lower opposite-width assumption. A retained child of chosen capacity at least three and a removed source child; arbitrary kept list. No exact-depth, youngest-marker, empty-history, convexity, singleton-end or recursive-potential premise. Only the next-band quadratic budget is concluded; m=k-5 and the top band remain separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_next_band_low_maximum_nonunit_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p=Ctx.Letter.ext j v → 1≤j)
  (s t : Ctx.Side) (hne : s≠t) (N x : ℕ)
  (hN : N∈σ.levels) (hNs : σ.sideAt N=s) (hx : x∈σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤σ.k-1)
  (keep : List ℕ) (m n p q : ℕ)
  (hm : 1≤m) (hlow : m≤σ.k-6) (hcoupling : m+n=σ.k-1)
  (hp : p∈(σ.part keep s m).childPositions)
  (hq : q∈σ.childPositions) (hremoved : q∉keep)
  (hcapacity : 3≤(match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p)) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (·∉keep)) t n
  (∀ f g, Ctx.Context.boundFuel f A+Ctx.Context.boundFuel g B≤(σ.k-2)^2-(σ.k-2)+1) ∧
    A.bound+B.bound≤(σ.k-2)^2-(σ.k-2)+1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (·∉keep)) t n
  let w := G σ t-1
  have hk : 7≤σ.k := by omega
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
  by_cases hwidth : 2≤w
  ·
    have hOne : 1∈A.levels := by simp [A,part_levels]
    have hqA : q∈A.extPositions 1 := by
      rw [part_extPositions_one hpositive keep s m]
      exact List.mem_filter.mpr ⟨hq,by simp [hremoved]⟩
    have hAside : A.sideAt 1=s := part_sideAt_one_of_mem hpositive keep s m hqA
    have hNpos : 1≤N := one_le_of_mem_levels hN
    have hOld : N+1∈A.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N,hN,rfl⟩)
    have hOldSide : A.sideAt (N+1)=s := (part_sideAt_succ σ keep s m hNpos).trans hNs
    have hxA : x∈A.extPositions (N+1) := by
      rw [part_extPositions_succ σ keep s m hNpos]
      exact hx
    have hAGlobal : G A s≤5 := by cases s <;> exact hglobal
    have hAWidth : 2≤G A t-1 := by cases t <;> exact hwidth
    have hPair := ctx_two_actual_marker_sharp_potential_arbitrary_history A hPosA s t hne
      1 (N+1) q x hOne hOld (by omega) hAside hOldSide hqA hxA hAGlobal hAWidth
    have hA : A.bound≤(w+1).choose 2+w-1 := by
      cases t <;> exact hPair.2
    have hw : w≤σ.k-2 := by change G σ t≤σ.k-1 at hopposite; dsimp only [w]; omega
    have hChoose := Nat.choose_le_choose 2 (Nat.add_le_add_right hw 1)
    have hA' : A.bound≤(σ.k-1).choose 2+(σ.k-2)-1 := by
      have he : σ.k-2+1=σ.k-1 := by omega
      rw [he] at hChoose
      omega
    have hCompanion := ctx_actual_marker_companion_maximum_bound σ hpositive s t hne N x
      hN hNs hx hglobal keep m n p q hp hq hremoved
    have hBraw := (hCompanion.2.2 hcapacity).2
    have hbudget : σ.k-n-1+1=m+1 := by omega
    have hB : B.bound≤(m+1).choose 2 := by simpa only [hbudget] using hBraw
    have hB' : B.bound≤(σ.k-5).choose 2 :=
      hB.trans (Nat.choose_le_choose 2 (by omega))
    have hNumeric (k : ℕ) (hk : 7≤k) :
        (k-1).choose 2+(k-2)-1+(k-5).choose 2≤(k-2)^2-(k-2)+1 := by
      let z := k-6
      have hz : 1≤z := by dsimp [z]; omega
      have h1 : k-1=z+5 := by dsimp [z]; omega
      have h2 : k-2=z+4 := by dsimp [z]; omega
      have h5 : k-5=z+1 := by dsimp [z]; omega
      rw [h1,h2,h5]
      have hc1 := Nat.choose_succ_right_eq (z+5) 1
      have hc2 := Nat.choose_succ_right_eq (z+1) 1
      simp only [Nat.reduceAdd,Nat.choose_one_right,
        show z+5-1=z+4 by omega,show z+1-1=z by omega] at hc1 hc2
      have hsubLeft := Nat.sub_add_cancel
        (show 1≤(z+5).choose 2+(z+4) by omega)
      have hsubRight := Nat.sub_add_cancel (show z+4≤(z+4)^2 by nlinarith)
      nlinarith
    have hFull := (Nat.add_le_add hA' hB').trans (hNumeric σ.k hk)
    have hFuelFull (ρ : Context) (fuel : ℕ) : boundFuel fuel ρ≤ρ.bound := by
      by_cases hf : ρ.childPositions.length+1≤fuel
      · exact (boundFuel_eq_bound ρ hf).le
      · exact boundFuel_mono (by omega : fuel≤ρ.childPositions.length+1) ρ
    exact ⟨fun f g => (Nat.add_le_add (hFuelFull _ f) (hFuelFull _ g)).trans hFull,hFull⟩
  · have hGt : G σ t≤2 := by dsimp only [w] at hwidth; omega
    have hSmall (ρ : Context)
        (hPos : ∀ p j v, ρ.letterAt p=Letter.ext j v → 1≤j)
        (hGs : G ρ s≤5) (hGt : G ρ t≤2) : ρ.bound≤4 := by
      have hh := ctx_small_global_axis_rank_region_potential ρ hPos t s (Ne.symm hne)
        (hGt.trans (by decide : 2≤3))
      have hb : ρ.bound≤G ρ s-1 := by
        cases s <;> exact hh.2.1.trans hh.2.2.1
      omega
    have hA4 : A.bound≤4 := hSmall A hPosA
      (by cases s <;> exact hglobal) (by cases t <;> exact hGt)
    have hB4 : B.bound≤4 := hSmall B
      (hPartPositive σ (σ.childPositions.filter (·∉keep)) t n)
      (by cases s <;> exact hglobal) (by cases t <;> exact hGt)
    have hz : 5≤σ.k-2 := by omega
    have hs : σ.k-2≤(σ.k-2)^2 := by nlinarith
    have hcancel := Nat.sub_add_cancel hs
    have hFull : A.bound+B.bound≤(σ.k-2)^2-(σ.k-2)+1 := by nlinarith
    have hFuelFull (ρ : Context) (fuel : ℕ) : boundFuel fuel ρ≤ρ.bound := by
      by_cases hf : ρ.childPositions.length+1≤fuel
      · exact (boundFuel_eq_bound ρ hf).le
      · exact boundFuel_mono (by omega : fuel≤ρ.childPositions.length+1) ρ
    exact ⟨fun f g => (Nat.add_le_add (hFuelFull _ f) (hFuelFull _ g)).trans hFull,hFull⟩


end ErdosSzekeres
