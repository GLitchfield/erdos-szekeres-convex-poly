import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Bound the opposite-kept internal cut of a thin three-rank-window context by 2k-4. The source-active opposite-kept rank span has one, two, or three ranks; two chosen-arm covers and two reserved opposite endpoint ranks pay the bound, with new-maximum normalization in the two-rank case. Positive labels, empty opposite history, opposite global at most k, k at least four, a source-active opposite-kept child, explicit two-arm separation and bracketing chosen children, and coupled positive maxima are required. No old large maximum, chosen-global cutoff, exact-depth, or recursive-potential hypothesis.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_three_rank_window_opposite_internal_cut_saturated_linear_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hclear : σ.levelsOn t 0 = [])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 4 ≤ σ.k) (L : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 2)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ σ.childPositions) (hqnot : q₀ ∉ keep)
  (hqcup : 0 < σ.cupLimit q₀ q₀) (hqcap : 0 < σ.capLimit q₀ q₀)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlkeep : l ∈ keep) (hrkeep : r ∈ keep)
  (hinside : ∀ q ∈ σ.childPositions, q ∉ keep → l < q ∧ q < r)
  (hseparated : ∀ p ∈ σ.childPositions, p ∈ keep →
    (∀ q ∈ σ.childPositions, q ∉ keep → p < q) ∨
    (∀ q ∈ σ.childPositions, q ∉ keep → q < p))
  (hm : 1 ≤ m) (hn : 1 ≤ n) (hsum : m + n = σ.k - 1) :
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ 2 * σ.k - 4) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 2 * σ.k - 4 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  have hOppositeσ : G σ t ≤ σ.k := by
    cases t <;> exact hopposite
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let lo (ρ : Context) (v : Side) (p : ℕ) := ρ.leftExt v 0 p+1
  let hi (ρ : Context) (v : Side) (p : ℕ) := G ρ v-1-ρ.rightExt v 0 p
  let ranks (ρ : Context) (v : Side) (p : ℕ) := Finset.Icc (lo ρ v p) (hi ρ v p)
  let Thin (ρ : Context) := ∀ p ∈ active ρ, hi ρ s p ≤ lo ρ s p+1
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
  have hThinσ : Thin σ := by
    intro p hp
    have hh := (hActive σ p).mp hp
    have ht := hthin p hh.1 hh.2.1 hh.2.2
    cases s <;> exact ht
  have hWindowσ (p : ℕ) (hp : p ∈ active σ) : L ≤ lo σ s p ∧ hi σ s p ≤ L+2 := by
    have hh := (hActive σ p).mp hp
    have hw := hwindow p hh.1 hh.2.1 hh.2.2
    cases s <;> exact hw
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
      (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
      (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
    cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
        have hpy : p ≤ y := by
          by_contra h
          have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hx
          exact List.not_mem_nil hx
        simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
    | some x =>
      have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
      have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hb
        rw [hnil] at hxq
        exact False.elim (List.not_mem_nil hxq)
      | some y =>
        have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
          rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
          exact Option.some.inj hb
        have hxy : x ≤ y := by
          simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
        simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
  have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
      (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
      (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
    cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        rw [hnil] at hyp
        exact False.elim (List.not_mem_nil hyp)
    | some x =>
      have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hb
        have hxq : x ≤ q := by
          by_contra h
          have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
          rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
          exact Option.some.inj ha
        have hxy : x ≤ y := by
          simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
        simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
  have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
      (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
      (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepLeft ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
      (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
      (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepRight ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.leftExt v top p ≤ ρ.leftExt v top q := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
  have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.rightExt v top q ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
  have hInherit (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (u : Side) (p : ℕ) :
      ρ.leftExt u 0 p ≤ (ρ.part keep v m).leftExt u 0 p ∧
      ρ.rightExt u 0 p ≤ (ρ.part keep v m).rightExt u 0 p := by
    let τ := ρ.part keep v m
    have hlevels (t : Ctx.Side) (N : ℕ) :
        List.Sublist ((ρ.levelsOn t N).map (· + 1)) (τ.levelsOn t (if N = 0 then 0 else N + 1)) := by
      unfold Ctx.Context.levelsOn
      change List.Sublist _ ((ρ.part keep v m).levels.filter _)
      rw [Ctx.Context.part_levels, List.filter_cons, List.filter_map]
      have heq : ρ.levels.filter (fun l => decide ((ρ.part keep v m).sideAt (l + 1) = t ∧
          ((if N = 0 then 0 else N + 1) = 0 ∨ l + 1 < (if N = 0 then 0 else N + 1)))) =
          ρ.levels.filter (fun l => decide (ρ.sideAt l = t ∧ (N = 0 ∨ l < N))) := by
        apply List.filter_congr
        intro l hl
        have hl1 := Ctx.Context.one_le_of_mem_levels hl
        by_cases hN : N = 0 <;>
          simp [hN, Ctx.Context.part_sideAt_succ ρ keep v m hl1]
      simp only [Function.comp_def]
      rw [heq]
      split_ifs <;> simp_all
    have hleft (t : Ctx.Side) (N p : ℕ) :
        ρ.leftExt t N p ≤ τ.leftExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.leftExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_leftStep_part_map ρ keep v m ls hpos (p, 0))).symm
    have hright (t : Ctx.Side) (N p : ℕ) :
        ρ.rightExt t N p ≤ τ.rightExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.rightExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_rightStep_part_map ρ keep v m ls hpos (p, 0))).symm
    exact ⟨by simpa only [if_pos rfl] using hleft u 0 p,
      by simpa only [if_pos rfl] using hright u 0 p⟩
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x l u, (ρ.part keep t m).letterAt x = Letter.ext l u → 1 ≤ l := by
    intro x l u hx
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
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx
      omega
  have hPartActive (ρ : Context) (keep : List ℕ) (v : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    have hle := ctx_part_limits_le ρ keep v m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, by simpa using hk⟩
  have hPartSide (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m q : ℕ) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) :
      (ρ.part keep v m).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hPos keep v m (q := q)
    rw [part_extPositions_one hPos keep v m]
    exact List.mem_filter.mpr ⟨hq, by simp [hnot]⟩
  have hMaxWitness : ∀ (xs : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ xs.sublists, ((xs.sublists.map f).max?).getD 0 = f ls := by
    intro xs f
    have hmem : f [] ∈ xs.sublists.map f := List.mem_map.mpr ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, he⟩ := List.mem_map.mp (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, he]⟩
  have hReserveLeft (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) (hqp : q < p) :
      ρ.leftExt v 0 q + 1 ≤ (ρ.part keep v m).leftExt v 0 p := by
    let τ := ρ.part keep v m
    let removed := ρ.childPositions.filter (· ∉ keep)
    let xs := removed.filter (· < p)
    have hqxs : q ∈ xs := by simp [xs, removed, hq, hnot, hqp]
    let x := xs.getLast (List.ne_nil_of_mem hqxs)
    have hqx : q ≤ x :=
      ((((childPositions_pairwise ρ).filter _).filter _).imp le_of_lt).rel_getLast hqxs
    have hext : τ.extPositions 1 = removed := part_extPositions_one hPos keep v m
    have hstep : leftStep τ (p, 0) 1 = (x, 1) := by
      simp only [leftStep, hext]
      change (match xs.getLast? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hqxs)]
    have hs := hPartSide ρ hPos keep v m q hq hnot
    have hlevels : τ.levelsOn v 0 = 1 :: (ρ.levelsOn v 0).map (· + 1) := part_levelsOn_self_zero hs
    obtain ⟨ls, hls, hval⟩ := hMaxWitness (ρ.levelsOn v 0)
      (fun ls => (ls.foldl (leftStep ρ) (x, 0)).2)
    change ρ.leftExt v 0 x = _ at hval
    have hlspos : ∀ j ∈ ls, 1 ≤ j := fun j hj =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hj)).1
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn v 0) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn v 0).sublists.map
      (fun xs => (xs.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.leftExt v 0 p at hv
    rw [List.foldl_cons, hstep, foldl_leftStep_part_map ρ keep v m ls hlspos,
      foldl_leftStep_count ρ ls x 1, ← hval] at hv
    have hmono := hLeftMono ρ v 0 q x hqx
    change ρ.leftExt v 0 q + 1 ≤ τ.leftExt v 0 p
    omega
  have hReserveRight (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) (hpq : p < q) :
      ρ.rightExt v 0 q + 1 ≤ (ρ.part keep v m).rightExt v 0 p := by
    let τ := ρ.part keep v m
    let removed := ρ.childPositions.filter (· ∉ keep)
    let xs := removed.filter (p < ·)
    have hqxs : q ∈ xs := by simp [xs, removed, hq, hnot, hpq]
    let x := xs.head (List.ne_nil_of_mem hqxs)
    have hxq : x ≤ q :=
      ((((childPositions_pairwise ρ).filter _).filter _).imp le_of_lt).rel_head hqxs
    have hext : τ.extPositions 1 = removed := part_extPositions_one hPos keep v m
    have hstep : rightStep τ (p, 0) 1 = (x, 1) := by
      simp only [rightStep, hext]
      change (match xs.head? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.head?_eq_some_head (List.ne_nil_of_mem hqxs)]
    have hs := hPartSide ρ hPos keep v m q hq hnot
    have hlevels : τ.levelsOn v 0 = 1 :: (ρ.levelsOn v 0).map (· + 1) := part_levelsOn_self_zero hs
    obtain ⟨ls, hls, hval⟩ := hMaxWitness (ρ.levelsOn v 0)
      (fun ls => (ls.foldl (rightStep ρ) (x, 0)).2)
    change ρ.rightExt v 0 x = _ at hval
    have hlspos : ∀ j ∈ ls, 1 ≤ j := fun j hj =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hj)).1
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn v 0) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn v 0).sublists.map
      (fun xs => (xs.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.rightExt v 0 p at hv
    rw [List.foldl_cons, hstep, foldl_rightStep_part_map ρ keep v m ls hlspos,
      foldl_rightStep_count ρ ls x 1, ← hval] at hv
    have hmono := hRightMono ρ v 0 x q hxq
    change ρ.rightExt v 0 q + 1 ≤ τ.rightExt v 0 p
    omega
  have hGPart (ρ : Context) (keep : List ℕ) (v u : Side) (m : ℕ) :
      G (ρ.part keep v m) u = G ρ u := by cases u <;> rfl
  have hInterval (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      lo ρ v p ≤ hi ρ v p := by
    have hc := (hActive ρ p).mp hp
    cases v <;> dsimp only [lo, hi, G, cupLimit, capLimit, chainExt] at hc ⊢ <;> omega
  have hRanksNonempty (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      (ranks ρ v p).Nonempty :=
    ⟨lo ρ v p, Finset.mem_Icc.mpr ⟨le_rfl, hInterval ρ v p hp⟩⟩
  have hEndpointsInherit (ρ : Context) (keep : List ℕ) (v u : Side) (m p : ℕ) :
      lo ρ u p ≤ lo (ρ.part keep v m) u p ∧ hi (ρ.part keep v m) u p ≤ hi ρ u p := by
    have hh := hInherit ρ keep v m u p
    dsimp only [lo, hi]
    rw [hGPart]
    omega
  have hRanksInherit (ρ : Context) (keep : List ℕ) (v u : Side) (m p : ℕ) :
      ranks (ρ.part keep v m) u p ⊆ ranks ρ u p := by
    intro z hz
    have hh := hEndpointsInherit ρ keep v u m p
    have hz' := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hThinPart (ρ : Context) (hThin : Thin ρ) (keep : List ℕ) (v : Side) (m : ℕ) :
      Thin (ρ.part keep v m) := by
    intro p hp
    have hs := hThin p (hPartActive ρ keep v m p hp).1
    have he := hEndpointsInherit ρ keep v s m p
    omega
  have hByCards (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hThin : Thin ρ) (X Y : Finset ℕ) (nx ny : ℕ)
      (hX : ∀ p ∈ active ρ, ranks ρ s p ⊆ X)
      (hY : ∀ p ∈ active ρ, ranks ρ t p ⊆ Y)
      (hx : X.card ≤ nx) (hy : Y.card ≤ ny) :
      ρ.bound ≤ (nx-1)*(ny-1)+1 := by
    let cost (I : Finset ℕ) := if I=∅ then 0 else
      ((I.biUnion (ranks ρ s)).card-1)*((I.biUnion (ranks ρ t)).card-1)+1
    have hThin' : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p → 0 < ρ.capLimit p p →
        G ρ s-1-ρ.rightExt s 0 p ≤ ρ.leftExt s 0 p+2 := by
      intro p hp hcu hca
      exact hThin p ((hActive ρ p).mpr ⟨hp,hcu,hca⟩)
    have hh := (ctx_thin_rank_rectangle_context_cover_potential ρ hPos s t hne
      (by cases s <;> exact hThin') [active ρ]
      (fun p hp => ⟨active ρ,by simp,hp⟩)
      (by intro I hI; have he := List.mem_singleton.mp hI; subst I; exact Finset.Subset.refl _)).2
    change ρ.bound ≤ ([active ρ].map cost).sum at hh
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hh
    apply hh.trans
    by_cases he : active ρ=∅
    · simp only [cost,if_pos he]; exact Nat.zero_le _
    have hSX : (active ρ).biUnion (ranks ρ s) ⊆ X := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      exact hX p hp hz
    have hSY : (active ρ).biUnion (ranks ρ t) ⊆ Y := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      exact hY p hp hz
    have hxc := (Finset.card_le_card hSX).trans hx
    have hyc := (Finset.card_le_card hSY).trans hy
    simp only [cost,if_neg he]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hFuelFull (ρ : Context) (f : ℕ) : boundFuel f ρ ≤ ρ.bound := by
    by_cases hf : ρ.childPositions.length+1 ≤ f
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : f ≤ ρ.childPositions.length+1) ρ
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  have hQ : l ∈ β.extPositions 1 := by
    rw [part_extPositions_one hpositive]
    have hnot : l ∉ rest := by simp [rest, hlkeep]
    exact List.mem_filter.mpr ⟨hl, by simp [hnot]⟩
  have hSide : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hQ
  have hOne : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hTerminal : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
    rw [hSide, part_levelsOn_self_zero hSide, hclear]
    simp
  let f : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext
        (if j = 1 then β.maxima.length else if 1 < j then j-1 else j) v
  let E : Context := {β with word := β.word.map f, maxima := β.maxima.eraseIdx 0}
  let ν : Context := match β.sideAt 1 with
    | Side.lower => {E with u := min β.u (β.k-β.maximumAt 1)}
    | Side.upper => {E with a := min β.a (β.k-β.maximumAt 1)}
  have hNorm := ctx_oldest_axis_maximum_erase_normalize β 1 hOne hTerminal
  have hToν : (∀ fuel, boundFuel fuel β ≤ boundFuel fuel ν) ∧ β.bound ≤ ν.bound :=
    ⟨hNorm.2.2.2.2.1, hNorm.2.2.2.2.2⟩
  let τ : Context := {σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ rest then Letter.child else Letter.ext (σ.maxima.length+1) t
      | Letter.ext j v => Letter.ext j v) }
  have hPrune := ctx_part_pruning_history_transport σ hpositive rest t n
  change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions.filter (· ∈ rest) ∧
    (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧ τ.sideAt j = σ.sideAt j) ∧
    (∀ v top, τ.levelsOn v top = σ.levelsOn v top) ∧
    (∀ v top p, τ.leftExt v top p = σ.leftExt v top p ∧
      τ.rightExt v top p = σ.rightExt v top p) ∧
    (∀ p q, τ.cupLimit p q = σ.cupLimit p q ∧ τ.capLimit p q = σ.capLimit p q) ∧
    active τ = (active σ).filter (· ∈ rest) ∧
    (∀ fuel, boundFuel fuel β ≤ boundFuel fuel τ) ∧ β.bound ≤ τ.bound at hPrune
  obtain ⟨hτPos, hτChild, hτHist, hτLevels, hτExt, hτLimits, hτActive, _, _⟩ := hPrune
  have hWord : β.word.map f = τ.word := by
    change ((List.range σ.word.length).map _).map f = (List.range σ.word.length).map _
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    cases he : σ.letterAt p with
    | child =>
      dsimp only [Function.comp_def]
      rw [he]
      by_cases hk : p ∈ rest
      · simp only [if_pos hk, f]
      · simp only [if_neg hk, f, if_pos rfl]
        rfl
    | ext j v =>
      have hj := hpositive p j v he
      dsimp only [Function.comp_def]
      rw [he]
      simp only [f, show j+1 ≠ 1 by omega, if_false, show 1 < j+1 by omega,
        if_true, Nat.add_sub_cancel]
  have hMaximum : β.maximumAt 1 = n := part_maximumAt_one σ rest t n
  have hνEq : ν = (match t with
      | Side.lower => {τ with u := min σ.u (σ.k-n)}
      | Side.upper => {τ with a := min σ.a (σ.k-n)}) := by
    cases t <;> simp only [ν, hSide, E, hWord, hMaximum]
    all_goals rfl
  have hνPos : ∀ p j v, ν.letterAt p = Letter.ext j v → 1 ≤ j := by
    cases t <;> rw [hνEq] <;> exact hτPos
  have hνChild : ν.childPositions = τ.childPositions := by cases t <;> rw [hνEq] <;> rfl
  have hνExt (v : Side) (p : ℕ) : ν.leftExt v 0 p = σ.leftExt v 0 p ∧
      ν.rightExt v 0 p = σ.rightExt v 0 p := by
    have he : ν.leftExt v 0 p = τ.leftExt v 0 p ∧ ν.rightExt v 0 p = τ.rightExt v 0 p := by
      cases t <;> rw [hνEq] <;> exact ⟨rfl, rfl⟩
    exact ⟨he.1.trans (hτExt v 0 p).1, he.2.trans (hτExt v 0 p).2⟩
  have hChosen : G ν s = G σ s := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · rw [hνEq]
    · rw [hνEq]
    · exact False.elim (hne rfl)
  have hOpposite : G ν t ≤ σ.k-n := by
    cases t <;> rw [hνEq]
    all_goals exact Nat.min_le_right _ _
  have hνLimits (p : ℕ) : ν.cupLimit p p ≤ τ.cupLimit p p ∧ ν.capLimit p p ≤ τ.capLimit p p := by
    cases t <;> rw [hνEq]
    · refine ⟨?_, le_rfl⟩
      exact min_le_min (Nat.sub_le_sub_right (Nat.sub_le_sub_right (Nat.min_le_left _ _) 1) _) le_rfl
    · refine ⟨le_rfl, ?_⟩
      exact min_le_min (Nat.sub_le_sub_right (Nat.sub_le_sub_right (Nat.min_le_left _ _) 1) _) le_rfl
  have hSource (p : ℕ) (hp : p ∈ active ν) : p ∈ active σ := by
    have hh := (hActive ν p).mp hp
    have hle := hνLimits p
    have hτ : p ∈ active τ := (hActive τ p).mpr ⟨by rw [← hνChild]; exact hh.1, by omega, by omega⟩
    rw [hτActive] at hτ
    exact (Finset.mem_filter.mp hτ).1
  have hThinν : Thin ν := by
    intro p hp
    have hh := hThinσ p (hSource p hp)
    dsimp only [hi,lo]
    rw [hChosen,(hνExt s p).1,(hνExt s p).2]
    exact hh
  have hνRanks (p : ℕ) : ranks ν s p = ranks σ s p := by
    simp only [ranks,lo,hi,hChosen,(hνExt s p).1,(hνExt s p).2]
  have hνRest (p : ℕ) (hp : p ∈ active ν) : p ∉ keep := by
    have hh := ((hActive ν p).mp hp).1
    rw [hνChild,hτChild] at hh
    have hr : p ∈ rest := of_decide_eq_true (List.mem_filter.mp hh).2
    exact of_decide_eq_true (List.mem_filter.mp hr).2
  have hPosA := hPositivePart σ keep s m
  have hPosB := hPositivePart σ rest t n
  have hThinA : Thin α := hThinPart σ hThinσ keep s m
  have hThinB : Thin β := hThinPart σ hThinσ rest t n
  have hAQ (p : ℕ) (hp : p ∈ active α) : p ∈ active σ ∧ p ∈ keep :=
    hPartActive σ keep s m p hp
  have hBQ (p : ℕ) (hp : p ∈ active β) : p ∈ active σ ∧ p ∉ keep := by
    have hh := hPartActive σ rest t n p hp
    exact ⟨hh.1,of_decide_eq_true (List.mem_filter.mp hh.2).2⟩
  have hQ₀ : q₀ ∈ active σ := (hActive σ q₀).mpr ⟨hq₀,hqcup,hqcap⟩
  have hWhole (p : ℕ) (hp : p ∈ active σ) : ranks σ s p ⊆ Finset.Icc L (L+2) := by
    intro z hz
    have hw := hWindowσ p hp
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hAEstimate (X : Finset ℕ) (nx : ℕ)
      (hX : ∀ p ∈ active α, ranks α s p ⊆ X) (hc : X.card ≤ nx) :
      α.bound ≤ (nx-1)*(σ.k-2)+1 := by
    have hh := hByCards α hPosA hThinA X (Finset.Icc 1 (σ.k-1)) nx (σ.k-1) hX
      (by
        intro p hp z hz
        have hzz := Finset.mem_Icc.mp hz
        have hg : G α t=G σ t := hGPart σ keep s t m
        dsimp only [lo,hi] at hzz
        rw [hg] at hzz
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
      hc (by simp <;> omega)
    have he : σ.k-1-1=σ.k-2 := by omega
    simpa only [he] using hh
  have hBEstimate (X : Finset ℕ) (nx : ℕ)
      (hX : ∀ p ∈ active σ, p ∉ keep → ranks σ s p ⊆ X) (hc : X.card ≤ nx) :
      β.bound ≤ (nx-1)*(m-1)+1 := by
    apply hToν.2.trans
    apply hByCards ν hνPos hThinν X (Finset.Icc 1 m) nx m
    · intro p hp
      rw [hνRanks]
      exact hX p (hSource p hp) (hνRest p hp)
    · intro p hp z hz
      have hh := Finset.mem_Icc.mp hz
      dsimp only [lo,hi] at hh
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · exact hc
    · simp
  let Q := (active σ).filter (· ∉ keep)
  have hQNon : Q.Nonempty := ⟨q₀,Finset.mem_filter.mpr ⟨hQ₀,hqnot⟩⟩
  let LB := (Q.image (lo σ s)).min' (hQNon.image _)
  let RB := (Q.image (hi σ s)).max' (hQNon.image _)
  obtain ⟨qL,hqL,heL⟩ := Finset.mem_image.mp (Finset.min'_mem (Q.image (lo σ s)) (hQNon.image _))
  obtain ⟨qR,hqR,heR⟩ := Finset.mem_image.mp (Finset.max'_mem (Q.image (hi σ s)) (hQNon.image _))
  change lo σ s qL=LB at heL
  change hi σ s qR=RB at heR
  have hQSource (q : ℕ) (hq : q ∈ Q) : q ∈ active σ ∧ q ∉ keep := Finset.mem_filter.mp hq
  have hLower (q : ℕ) (hq : q ∈ Q) : LB ≤ lo σ s q :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hUpper (q : ℕ) (hq : q ∈ Q) : hi σ s q ≤ RB :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hSpan : L ≤ LB ∧ LB ≤ RB ∧ RB ≤ L+2 := by
    have hWL := hWindowσ qL (hQSource qL hqL).1
    have hWR := hWindowσ qR (hQSource qR hqR).1
    have hIL := hInterval σ s qL (hQSource qL hqL).1
    have hUR := hUpper qL hqL
    omega
  have hQBox (q : ℕ) (hq : q ∈ active σ) (hqn : q ∉ keep) :
      ranks σ s q ⊆ Finset.Icc LB RB := by
    intro z hz
    have hqQ : q ∈ Q := Finset.mem_filter.mpr ⟨hq,hqn⟩
    have hLo := hLower q hqQ
    have hHi := hUpper q hqQ
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  let AL := (active α).filter (fun p => p<q₀)
  let AR := (active α).filter (fun p => q₀<p)
  have hALOrder (p : ℕ) (hp : p ∈ AL) (q : ℕ) (hq : q ∈ Q) : p<q := by
    have hpa := Finset.mem_filter.mp hp
    have hs := hAQ p hpa.1
    have hpc := ((hActive σ p).mp hs.1).1
    have hqs := hQSource q hq
    have hqc := ((hActive σ q).mp hqs.1).1
    rcases hseparated p hpc hs.2 with ha | hb
    · exact ha q hqc hqs.2
    · have hh := hb q₀ hq₀ hqnot
      omega
  have hAROrder (p : ℕ) (hp : p ∈ AR) (q : ℕ) (hq : q ∈ Q) : q<p := by
    have hpa := Finset.mem_filter.mp hp
    have hs := hAQ p hpa.1
    have hpc := ((hActive σ p).mp hs.1).1
    have hqs := hQSource q hq
    have hqc := ((hActive σ q).mp hqs.1).1
    rcases hseparated p hpc hs.2 with ha | hb
    · have hh := ha q₀ hq₀ hqnot
      omega
    · exact hb q hqc hqs.2
  have hSides (p : ℕ) (hp : p ∈ active α) : p ∈ AL ∨ p ∈ AR := by
    have hne' : p≠q₀ := by intro he; subst p; exact hqnot (hAQ q₀ hp).2
    by_cases hlt : p<q₀
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp,hlt⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  have hStrictLeft (p : ℕ) (hp : p ∈ AL) (q : ℕ) (hq : q ∈ Q)
      (z : ℕ) (hz : z ∈ ranks α s p) : z < hi σ s q := by
    have hqs := hQSource q hq
    have hqc := ((hActive σ q).mp hqs.1).1
    have hr := hReserveRight σ hpositive keep s m p q hqc hqs.2 (hALOrder p hp q hq)
    change _ ≤ α.rightExt s 0 p at hr
    have hh := Finset.mem_Icc.mp hz
    have hg : G α s=G σ s := hGPart σ keep s s m
    dsimp only [lo,hi] at hh ⊢
    rw [hg] at hh
    omega
  have hStrictRight (p : ℕ) (hp : p ∈ AR) (q : ℕ) (hq : q ∈ Q)
      (z : ℕ) (hz : z ∈ ranks α s p) : lo σ s q < z := by
    have hqs := hQSource q hq
    have hqc := ((hActive σ q).mp hqs.1).1
    have hr := hReserveLeft σ hpositive keep s m p q hqc hqs.2 (hAROrder p hp q hq)
    change _ ≤ α.leftExt s 0 p at hr
    have hh := (Finset.mem_Icc.mp hz).1
    dsimp only [lo] at hh ⊢
    omega
  have hALBox (p : ℕ) (hp : p ∈ AL) : ranks α s p ⊆ Finset.Icc L LB := by
    intro z hz
    have hs := hAQ p (Finset.mem_filter.mp hp).1
    have hw := Finset.mem_Icc.mp (hWhole p hs.1 (hRanksInherit σ keep s s m p hz))
    have hh := hStrictLeft p hp qL hqL z hz
    have ht := hThinσ qL (hQSource qL hqL).1
    exact Finset.mem_Icc.mpr ⟨hw.1,by omega⟩
  have hARBox (p : ℕ) (hp : p ∈ AR) : ranks α s p ⊆ Finset.Icc RB (L+2) := by
    intro z hz
    have hs := hAQ p (Finset.mem_filter.mp hp).1
    have hw := Finset.mem_Icc.mp (hWhole p hs.1 (hRanksInherit σ keep s s m p hz))
    have hh := hStrictRight p hp qR hqR z hz
    have ht := hThinσ qR (hQSource qR hqR).1
    exact Finset.mem_Icc.mpr ⟨by omega,hw.2⟩
  let cost (I : Finset ℕ) := if I=∅ then 0 else
    ((I.biUnion (ranks α s)).card-1)*((I.biUnion (ranks α t)).card-1)+1
  have hCost (I X : Finset ℕ) (a : ℕ) (hI : I ⊆ active α)
      (hX : ∀ p ∈ I, ranks α s p ⊆ X) (hx : X.card ≤ a+1) :
      cost I ≤ a*(σ.k-2)+1 := by
    by_cases he : I=∅
    · simp only [cost,if_pos he]; exact Nat.zero_le _
    have hSX : I.biUnion (ranks α s) ⊆ X := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      exact hX p hp hz
    have hSY : I.biUnion (ranks α t) ⊆ Finset.Icc 1 (σ.k-1) := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      have hg : G α t=G σ t := hGPart σ keep s t m
      dsimp only [lo,hi] at hh
      rw [hg] at hh
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hxc := (Finset.card_le_card hSX).trans hx
    have hyc : (I.biUnion (ranks α t)).card ≤ σ.k-1 := by
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using Finset.card_le_card hSY
    simp only [cost,if_neg he]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hThinA' : ∀ p ∈ α.childPositions, 0 < α.cupLimit p p → 0 < α.capLimit p p →
      G α s-1-α.rightExt s 0 p ≤ α.leftExt s 0 p+2 := by
    intro p hp hcu hca
    exact hThinA p ((hActive α p).mpr ⟨hp,hcu,hca⟩)
  have hTwoCover := (ctx_thin_rank_rectangle_context_cover_potential α hPosA s t hne
    (by cases s <;> exact hThinA') [AL,AR]
    (by
      intro p hp
      rcases hSides p hp with hh | hh
      · exact ⟨AL,by simp,hh⟩
      · exact ⟨AR,by simp,hh⟩)
    (by
      intro I hI
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hI
      rcases hI with rfl | rfl
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _)).2
  change α.bound ≤ ([AL,AR].map cost).sum at hTwoCover
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hTwoCover
  have hLeftCost : cost AL ≤ (LB-L)*(σ.k-2)+1 :=
    hCost AL (Finset.Icc L LB) (LB-L) (Finset.filter_subset _ _) hALBox
      (by simp only [Nat.card_Icc]; omega)
  have hRightCost : cost AR ≤ (L+2-RB)*(σ.k-2)+1 :=
    hCost AR (Finset.Icc RB (L+2)) (L+2-RB) (Finset.filter_subset _ _) hARBox
      (by simp only [Nat.card_Icc]; omega)
  have hAArms : α.bound ≤ (LB-L)*(σ.k-2)+(L+2-RB)*(σ.k-2)+2 := by omega
  have hBRaw : β.bound ≤ (RB-LB)*(σ.k-4)+1 := by
    have hX : ∀ p ∈ active β, ranks β s p ⊆ Finset.Icc LB RB := by
      intro p hp
      have hs := hBQ p hp
      exact (hRanksInherit σ rest t s n p).trans (hQBox p hs.1 hs.2)
    have hY : ∀ p ∈ active β, ranks β t p ⊆ Finset.Icc 2 (σ.k-2) := by
      intro p hp z hz
      have hs := hBQ p hp
      have hpc := ((hActive σ p).mp hs.1).1
      have hb := hinside p hpc hs.2
      have hnl : l ∉ rest := by simp [rest,hlkeep]
      have hnr : r ∉ rest := by simp [rest,hrkeep]
      have hleft := hReserveLeft σ hpositive rest t n p l hl hnl hb.1
      change _ ≤ β.leftExt t 0 p at hleft
      have hright := hReserveRight σ hpositive rest t n p r hr hnr hb.2
      change _ ≤ β.rightExt t 0 p at hright
      have hh := Finset.mem_Icc.mp hz
      have hg : G β t=G σ t := hGPart σ rest t t n
      dsimp only [lo,hi] at hh
      rw [hg] at hh
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hh := hByCards β hPosB hThinB (Finset.Icc LB RB) (Finset.Icc 2 (σ.k-2))
      (RB-LB+1) (σ.k-3) hX hY
      (by simp only [Nat.card_Icc]; omega) (by simp only [Nat.card_Icc]; omega)
    have he₁ : RB-LB+1-1=RB-LB := by omega
    have he₂ : σ.k-3-1=σ.k-4 := by omega
    simpa only [he₁,he₂] using hh
  have hBNormalized : β.bound ≤ (RB-LB)*(m-1)+1 := by
    have hh := hBEstimate (Finset.Icc LB RB) (RB-LB+1) hQBox
      (by simp only [Nat.card_Icc]; omega)
    simpa only [Nat.add_sub_cancel] using hh
  have hALinear (hlarge : σ.k-3 ≤ m) : α.bound ≤ σ.k-1 := by
    have hAside : α.sideAt 1=s := hPartSide σ hpositive keep s m q₀ hq₀ hqnot
    have hAlevel : 1 ∈ α.levels := by simp only [α,part_levels,List.mem_cons,true_or]
    have hAmax : α.maximumAt 1=m := part_maximumAt_one σ keep s m
    let μ : Context := match s with
      | Side.lower => {α with u:=min α.u (α.k-m), maxima:=[]}
      | Side.upper => {α with a:=min α.a (α.k-m), maxima:=[]}
    have hμLetter (p : ℕ) : μ.letterAt p=α.letterAt p := by cases s <;> rfl
    have hμPos : ∀ p j v, μ.letterAt p=Letter.ext j v → 1≤j := by
      intro p j v hp
      rw [hμLetter] at hp
      exact hPosA p j v hp
    have hμSmall : G μ s≤3 := by
      cases s <;> simp only [G,μ]
      all_goals exact (Nat.min_le_right _ _).trans (show σ.k-m≤3 by omega)
    have hμOpp : G μ t=G σ t := by
      cases s <;> cases t
      · exact False.elim (hne rfl)
      · rfl
      · rfl
      · exact False.elim (hne rfl)
    have hNorm := ctx_sibling_maximum_upper_normalize α 1 hAlevel
    have hToμ : α.bound≤μ.bound := by
      cases s <;> simpa only [μ,hAside,hAmax,Nat.sub_self,List.take_zero] using hNorm.2.2
    have hh := ctx_small_global_axis_rank_region_potential μ hμPos s t hne hμSmall
    have hb : μ.bound≤G μ t-1 := by
      cases t <;> exact hh.2.1.trans hh.2.2.1
    rw [hμOpp] at hb
    exact hToμ.trans (hb.trans (Nat.sub_le_sub_right hOppositeσ 1))
  have hSum : α.bound+β.bound≤2*σ.k-4 := by
    by_cases he : RB=LB
    · have hA : α.bound≤σ.k-1 := by
        have hX : ∀ p ∈ active α, ranks α s p ⊆ (Finset.Icc L (L+2)).erase LB := by
          intro p hp z hz
          have hs := hAQ p hp
          have hw := hWhole p hs.1 (hRanksInherit σ keep s s m p hz)
          apply Finset.mem_erase.mpr
          refine ⟨?_,hw⟩
          intro hzEq
          have hqQ : q₀ ∈ Q := Finset.mem_filter.mpr ⟨hQ₀,hqnot⟩
          rcases hSides p hp with hL | hR
          · have hh := hStrictLeft p hL q₀ hqQ z hz
            have hu := hUpper q₀ hqQ
            omega
          · have hh := hStrictRight p hR q₀ hqQ z hz
            have hl := hLower q₀ hqQ
            omega
        have hLBmem : LB ∈ Finset.Icc L (L+2) := Finset.mem_Icc.mpr ⟨hSpan.1,by omega⟩
        have hc : ((Finset.Icc L (L+2)).erase LB).card ≤ 2 := by
          rw [Finset.card_erase_of_mem hLBmem]
          simp only [Nat.card_Icc]
          omega
        have hh := hAEstimate ((Finset.Icc L (L+2)).erase LB) 2 hX hc
        norm_num only [Nat.reduceSub,Nat.one_mul] at hh
        omega
      have hB : β.bound≤1 := by simpa only [he,Nat.sub_self,Nat.zero_mul,Nat.zero_add] using hBNormalized
      omega
    by_cases he₁ : RB=LB+1
    · have hcoef : LB-L+(L+2-RB)=1 := by omega
      have hA : α.bound≤σ.k := by
        have hh := hAArms
        rw [← Nat.add_mul,hcoef,Nat.one_mul] at hh
        omega
      have hB : β.bound≤m := by
        have hh := hBNormalized
        rw [he₁,Nat.add_sub_cancel_left,Nat.one_mul] at hh
        omega
      by_cases hsmall : m≤σ.k-4
      · omega
      · have ha := hALinear (by omega)
        have hb := hBRaw
        rw [he₁,Nat.add_sub_cancel_left,Nat.one_mul] at hb
        omega
    · have he₂ : RB=LB+2 := by omega
      have hcoef : LB-L+(L+2-RB)=0 := by omega
      have hA : α.bound≤2 := by
        have hh := hAArms
        rw [← Nat.add_mul,hcoef,Nat.zero_mul,Nat.zero_add] at hh
        exact hh
      have hb := hBRaw
      rw [he₂,Nat.add_sub_cancel_left] at hb
      omega
  exact ⟨fun f g => (Nat.add_le_add (hFuelFull α f) (hFuelFull β g)).trans hSum,hSum⟩


end ErdosSzekeres
