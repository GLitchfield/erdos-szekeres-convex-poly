import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential
import ESBlueprint.B.CtxLargeChosenMaximumBracketedPartUnitBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Prove the four-rank next-band internally bracketed chosen-part cut saving from an active retained rank witness. Positive labels, opposite global at most k-1, k at least five, an indexed chosen maximum at least k-4, thin active pure chosen intervals in a four-rank window, and complementary physical brackets suffice. The active chosen-part rank forces a gap of at least two between the complementary source-arm endpoint ranks. Two raw opposite-arm covers cost at most3k-10, while the old maximum gives chosen bound at most one, so the full cut and all independent fuel approximations are at most3k-9. Opposite history and new maxima are unrestricted. No coupling, positive-maxima, actual occurrence at the old level, chosen-global, exact-depth, interval-convexity or recursive-potential premise is used.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_four_rank_next_band_chosen_internal_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1)
  (hk : 5 ≤ σ.k) (N L : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s)
  (hmaximum : σ.k - 4 ≤ σ.maximumAt N)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 3)
  (keep : List ℕ) (p₀ l r m n : ℕ)
  (hp₀ : p₀ ∈ σ.childPositions) (hpkeep : p₀ ∈ keep)
  (hpcup : 0 < (σ.part keep s m).cupLimit p₀ p₀)
  (hpcap : 0 < (σ.part keep s m).capLimit p₀ p₀)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ σ.childPositions, p ∈ keep → l < p ∧ p < r) :
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ 3 * σ.k - 9) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 3 * σ.k - 9 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  have hOppositeσ : G σ t ≤ σ.k - 1 := by
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
  have hWindowσ (p : ℕ) (hp : p ∈ active σ) : L ≤ lo σ s p ∧ hi σ s p ≤ L+3 := by
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
  have hPosA := hPositivePart σ keep s m
  have hPosB := hPositivePart σ rest t n
  have hThinB : Thin β := hThinPart σ hThinσ rest t n
  have hBQ (p : ℕ) (hp : p ∈ active β) : p ∈ active σ ∧ p ∉ keep := by
    have hh := hPartActive σ rest t n p hp
    exact ⟨hh.1,of_decide_eq_true (List.mem_filter.mp hh.2).2⟩
  have hP : p₀ ∈ active α := by
    apply (hActive α p₀).mpr
    refine ⟨?_,hpcup,hpcap⟩
    rw [part_childPositions]
    exact List.mem_filter.mpr ⟨hp₀,by simp [hpkeep]⟩
  have hNotRest : p₀ ∉ rest := by simp [rest,hpkeep]
  have hUnit := ctx_large_chosen_maximum_bracketed_part_unit_bound σ hpositive s N hN hNs
    hmaximum keep m l r hl hr hlnot hrnot hinside
  let BL := (active β).filter (fun q => q<p₀)
  let BR := (active β).filter (fun q => p₀<q)
  let QL := (active σ).filter (fun q => q∉keep ∧ q<p₀)
  let QR := (active σ).filter (fun q => q∉keep ∧ p₀<q)
  have hBLSource (q : ℕ) (hq : q ∈ BL) : q ∈ QL := by
    have hh := Finset.mem_filter.mp hq
    have hs := hBQ q hh.1
    exact Finset.mem_filter.mpr ⟨hs.1,hs.2,hh.2⟩
  have hBRSource (q : ℕ) (hq : q ∈ BR) : q ∈ QR := by
    have hh := Finset.mem_filter.mp hq
    have hs := hBQ q hh.1
    exact Finset.mem_filter.mpr ⟨hs.1,hs.2,hh.2⟩
  have hSplit (q : ℕ) (hq : q ∈ active β) : q ∈ BL ∨ q ∈ BR := by
    have hne' : q≠p₀ := by intro he; subst q; exact (hBQ p₀ hq).2 hpkeep
    by_cases hh : q<p₀
    · exact Or.inl (Finset.mem_filter.mpr ⟨hq,hh⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hq,by omega⟩)
  have hWhole (q : ℕ) (hq : q ∈ active σ) : ranks σ s q ⊆ Finset.Icc L (L+3) := by
    intro z hz
    have hw := hWindowσ q hq
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  let cost (I : Finset ℕ) := if I=∅ then 0 else
    ((I.biUnion (ranks β s)).card-1)*((I.biUnion (ranks β t)).card-1)+1
  have hThinB' : ∀ q ∈ β.childPositions, 0 < β.cupLimit q q → 0 < β.capLimit q q →
      G β s-1-β.rightExt s 0 q ≤ β.leftExt s 0 q+2 := by
    intro q hq hc hu
    exact hThinB q ((hActive β q).mpr ⟨hq,hc,hu⟩)
  have hCover := (ctx_thin_rank_rectangle_context_cover_potential β hPosB s t hne
    (by cases s <;> exact hThinB') [BL,BR]
    (by
      intro q hq
      rcases hSplit q hq with hh | hh
      · exact ⟨BL,by simp,hh⟩
      · exact ⟨BR,by simp,hh⟩)
    (by
      intro I hI
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hI
      rcases hI with rfl | rfl
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _)).2
  change β.bound ≤ ([BL,BR].map cost).sum at hCover
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hCover
  have hCost (I X : Finset ℕ) (a : ℕ) (dir : Bool)
      (hI : I ⊆ active β)
      (hX : ∀ q ∈ I, ranks β s q ⊆ X) (hx : X.card ≤ a)
      (horder : ∀ q ∈ I, if dir then q<p₀ else p₀<q) :
      cost I ≤ (a-1)*(σ.k-4)+1 := by
    by_cases he : I=∅
    · simp only [cost,if_pos he]; exact Nat.zero_le _
    have hSX : I.biUnion (ranks β s) ⊆ X := by
      intro z hz
      obtain ⟨q,hq,hz⟩ := Finset.mem_biUnion.mp hz
      exact hX q hq hz
    let Y := if dir then Finset.Icc 1 (σ.k-3) else Finset.Icc 2 (σ.k-2)
    have hSY : I.biUnion (ranks β t) ⊆ Y := by
      intro z hz
      obtain ⟨q,hq,hz⟩ := Finset.mem_biUnion.mp hz
      have hs := horder q hq
      have hh := Finset.mem_Icc.mp hz
      have hg : G β t=G σ t := hGPart σ rest t t n
      dsimp only [lo,hi] at hh
      rw [hg] at hh
      cases dir with
      | false =>
        have hr := hReserveLeft σ hpositive rest t n q p₀ hp₀ hNotRest hs
        change _ ≤ β.leftExt t 0 q at hr
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      | true =>
        have hr := hReserveRight σ hpositive rest t n q p₀ hp₀ hNotRest hs
        change _ ≤ β.rightExt t 0 q at hr
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hYCard : Y.card ≤ σ.k-3 := by cases dir <;> simp [Y,Nat.card_Icc] <;> omega
    have hxc := (Finset.card_le_card hSX).trans hx
    have hyc := (Finset.card_le_card hSY).trans hYCard
    simp only [cost,if_neg he]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hLeftWhole : cost BL ≤ 3*σ.k-11 := by
    have hh := hCost BL (Finset.Icc L (L+3)) 4 true (Finset.filter_subset _ _)
      (by
        intro q hq
        have hs := hBQ q (Finset.mem_filter.mp hq).1
        exact (hRanksInherit σ rest t s n q).trans (hWhole q hs.1))
      (by simp <;> omega) (by intro q hq; exact (Finset.mem_filter.mp hq).2)
    norm_num only [Nat.reduceSub] at hh
    omega
  have hRightWhole : cost BR ≤ 3*σ.k-11 := by
    have hh := hCost BR (Finset.Icc L (L+3)) 4 false (Finset.filter_subset _ _)
      (by
        intro q hq
        have hs := hBQ q (Finset.mem_filter.mp hq).1
        exact (hRanksInherit σ rest t s n q).trans (hWhole q hs.1))
      (by simp <;> omega) (by intro q hq; exact (Finset.mem_filter.mp hq).2)
    norm_num only [Nat.reduceSub] at hh
    omega
  have hBBudget : β.bound ≤ 3*σ.k-10 := by
    by_cases hQL : QL.Nonempty
    · by_cases hQR : QR.Nonempty
      · let LB := (QL.image (lo σ s)).max' (hQL.image _)
        let RB := (QR.image (hi σ s)).min' (hQR.image _)
        obtain ⟨qL,hqL,heL⟩ := Finset.mem_image.mp
          (Finset.max'_mem (QL.image (lo σ s)) (hQL.image _))
        obtain ⟨qR,hqR,heR⟩ := Finset.mem_image.mp
          (Finset.min'_mem (QR.image (hi σ s)) (hQR.image _))
        change lo σ s qL=LB at heL
        change hi σ s qR=RB at heR
        have hLeftMax (q : ℕ) (hq : q ∈ QL) : lo σ s q ≤ LB :=
          Finset.le_max' _ _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hRightMin (q : ℕ) (hq : q ∈ QR) : RB ≤ hi σ s q :=
          Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hLdata := Finset.mem_filter.mp hqL
        have hRdata := Finset.mem_filter.mp hqR
        have hWL := hWindowσ qL hLdata.1
        have hWR := hWindowσ qR hRdata.1
        have hIL := hInterval σ s qL hLdata.1
        have hIR := hInterval σ s qR hRdata.1
        have hRange : L ≤ LB ∧ RB ≤ L+3 := by omega
        let z := lo α s p₀
        have hz : z ∈ ranks α s p₀ := Finset.mem_Icc.mpr ⟨le_rfl,hInterval α s p₀ hP⟩
        have hGap : LB+2 ≤ RB := by
          have hLc := ((hActive σ qL).mp hLdata.1).1
          have hRc := ((hActive σ qR).mp hRdata.1).1
          have hresL := hReserveLeft σ hpositive keep s m p₀ qL hLc hLdata.2.1 hLdata.2.2
          change _ ≤ α.leftExt s 0 p₀ at hresL
          have hresR := hReserveRight σ hpositive keep s m p₀ qR hRc hRdata.2.1 hRdata.2.2
          change _ ≤ α.rightExt s 0 p₀ at hresR
          have hzz := Finset.mem_Icc.mp hz
          have hg : G α s=G σ s := hGPart σ keep s s m
          dsimp only [lo,hi] at heL heR hzz
          rw [hg] at hzz
          omega
        let a := LB+2-L
        let b := L+4-(RB-1)
        have hLeft : cost BL ≤ (a-1)*(σ.k-4)+1 := by
          apply hCost BL (Finset.Icc L (LB+1)) a true (Finset.filter_subset _ _)
          · intro q hq v hv
            have hqs := Finset.mem_filter.mp (hBLSource q hq)
            have hmax := hLeftMax q (hBLSource q hq)
            have ht := hThinσ q hqs.1
            have hw := hWindowσ q hqs.1
            have hh := Finset.mem_Icc.mp (hRanksInherit σ rest t s n q hv)
            exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
          · simp only [Nat.card_Icc,a]
            omega
          · intro q hq; exact (Finset.mem_filter.mp hq).2
        have hRight : cost BR ≤ (b-1)*(σ.k-4)+1 := by
          apply hCost BR (Finset.Icc (RB-1) (L+3)) b false (Finset.filter_subset _ _)
          · intro q hq v hv
            have hqs := Finset.mem_filter.mp (hBRSource q hq)
            have hmin := hRightMin q (hBRSource q hq)
            have ht := hThinσ q hqs.1
            have hw := hWindowσ q hqs.1
            have hh := Finset.mem_Icc.mp (hRanksInherit σ rest t s n q hv)
            exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
          · simp only [Nat.card_Icc,b]
            omega
          · intro q hq; exact (Finset.mem_filter.mp hq).2
        have hcoef : (a-1)+(b-1) ≤ 3 := by dsimp [a,b]; omega
        have hmul := Nat.mul_le_mul_right (σ.k-4) hcoef
        rw [Nat.add_mul] at hmul
        omega
      · have hEmpty : BR=∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro q hq
          exact hQR ⟨q,hBRSource q hq⟩
        have he : cost BR=0 := by simp only [cost,hEmpty,if_pos rfl]
        omega
    · have hEmpty : BL=∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        exact hQL ⟨q,hBLSource q hq⟩
      have he : cost BL=0 := by simp only [cost,hEmpty,if_pos rfl]
      omega
  have hSum : α.bound+β.bound ≤ 3*σ.k-9 := by
    have hu : α.bound ≤ 1 := hUnit.2
    omega
  exact ⟨fun f g => (Nat.add_le_add (hFuelFull α f) (hFuelFull β g)).trans hSum,hSum⟩


end ErdosSzekeres
