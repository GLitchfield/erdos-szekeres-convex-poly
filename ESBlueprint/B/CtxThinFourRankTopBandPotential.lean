import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential
import ESBlueprint.B.CtxThinFourRankTopBandChosenInternalCutBound
import ESBlueprint.B.CtxThinFourRankTopBandEndpointCutBound
import ESBlueprint.B.CtxThinFourRankTopBandOppositeInternalCutBound
import ESBlueprint.B.CtxActualMarkerSaturatedLinearPotential
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxBoundAttainedByEndCut

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Close the whole four-rank top-band potential by classifying all legal cuts into the three prepared geometries. A source-inactive opposite part is zero, while the old-maximum normalization leaves an actual chosen marker and pays the remaining part. The complete cut bounds imply every fuel approximation and the full context bound are at most 3k-8.
Positive labels, distinct axes, empty indexed opposite history, opposite global at most k, k at least five, and some indexed chosen maximum at least k-4.
Every source-active pure chosen interval has width at most two and lies inside one four-rank window.
No actual occurrence at the selected old level, chosen-global, exact-depth, child pattern, recursive or cut-bound premise. The large old maximum and empty opposite history remain substantive restrictions.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_four_rank_top_band_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (hclear : σ.levelsOn t 0 = [])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 5 ≤ σ.k) (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s)
  (hmaximum : σ.k - 4 ≤ σ.maximumAt N) (L : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 3) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3 * σ.k - 8) ∧ σ.bound ≤ 3 * σ.k - 8 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
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
  have hBaseLower (c p k : ℕ) (hc : c ≤ 2) (hp : p ≤ k - 1) : baseOf c p k ≤ p := by
    unfold baseOf
    by_cases hz : c = 0 ∨ p = 0
    · rw [if_pos hz]
      exact Nat.zero_le _
    rw [if_neg hz]
    by_cases ho : c = 1 ∨ p = 1
    · rw [if_pos ho]
      omega
    rw [if_neg ho]
    have hc2 : c = 2 := by omega
    subst c
    rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : p + 1 + (2 + 1) - 4 = p := by omega
    have hcol : p + 1 - 2 = p - 1 := by omega
    rw [hrow, hcol, Nat.choose_symm (show 1 ≤ p by omega)]
    simp
  have hBaseUpper (c p k : ℕ) (hp : p ≤ 2) (hc : c ≤ k - 1) : baseOf c p k ≤ c := by
    unfold baseOf
    by_cases hz : c = 0 ∨ p = 0
    · rw [if_pos hz]
      exact Nat.zero_le _
    rw [if_neg hz]
    by_cases ho : c = 1 ∨ p = 1
    · rw [if_pos ho]
      omega
    rw [if_neg ho]
    have hp2 : p = 2 := by omega
    subst p
    rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : 2 + 1 + (c + 1) - 4 = c := by omega
    rw [hrow]
    simp
  have hBlockConvex (ρ : Context) (ks : List ℕ) (hk : ks ∈ ρ.blocks) : Convex ρ ks := by
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hk
    have hinfix : ks <:+: ρ.childPositions := by
      refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨pre, post, he⟩ := hinfix
    have he' : pre ++ (ks ++ post) = ρ.childPositions := by simpa only [List.append_assoc] using he
    have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
      rw [he']
      exact childPositions_pairwise ρ
    have hbefore : ∀ a ∈ pre, ∀ b ∈ ks, a < b := by
      intro a ha b hb
      exact (List.pairwise_append.mp hs).2.2 a ha b (List.mem_append_left post hb)
    have hafter : ∀ a ∈ ks, ∀ b ∈ post, a < b :=
      (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).2.2
    intro a ha b hb z hz haz hzb
    rw [← he'] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have hh := hbefore z hz a ha
      omega
    · rcases List.mem_append.mp hz with hz | hz
      · exact hz
      · have hh := hafter b hb z hz
        omega
  have hOutside (ρ : Context) (ks : List ℕ) (hconv : Convex ρ ks)
      (a b z : ℕ) (ha : a ∈ ks) (hb : b ∈ ks) (hz : z ∈ ρ.childPositions) (hzn : z ∉ ks) :
      z < min a b ∨ max a b < z := by
    by_contra h
    by_cases hab : a ≤ b
    · exact hzn (hconv a ha b hb z hz (by omega) (by omega))
    · exact hzn (hconv b hb a ha z hz (by omega) (by omega))
  have hFuelFull (ρ : Context) (f : ℕ) : boundFuel f ρ≤ρ.bound := by
    by_cases hf : ρ.childPositions.length+1≤f
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : f≤ρ.childPositions.length+1) ρ
  have hZero (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p=Letter.ext j v → 1≤j)
      (hNo : ∀ p ∈ ρ.childPositions, 0<ρ.cupLimit p p → 0<ρ.capLimit p p → False) :
      ρ.bound=0 := by
    have hh := (ctx_thin_rank_rectangle_context_cover_potential ρ hPos s t hne
      (by intro p hp hcu hca; exact False.elim (hNo p hp hcu hca)) []
      (by
        intro p hp
        have ha := (hActive ρ p).mp hp
        exact False.elim (hNo p ha.1 ha.2.1 ha.2.2))
      (by simp)).2
    simpa using hh
  have hBase : σ.base≤3*σ.k-8 := by
    rw [base_eq_baseOf]
    cases he : σ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      change baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k ≤ 3*σ.k-8
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      by_cases hz : σ.cupLimit p p=0 ∨ σ.capLimit p p=0
      · simp [baseOf,hz]
      have ht := hthin p hp (by omega) (by omega)
      have hc : (match s with | Side.lower=>σ.cupLimit p p | Side.upper=>σ.capLimit p p)≤2 := by
        cases s <;> simp only [cupLimit,capLimit,chainExt] at ht ⊢ <;> omega
      have hcu : σ.cupLimit p p≤σ.k-1 := by dsimp only [cupLimit]; omega
      have hca : σ.capLimit p p≤σ.k-1 := by dsimp only [capLimit]; omega
      have hb : baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k≤σ.k-1 := by
        cases s
        · exact (hBaseLower _ _ _ hc hca).trans hca
        · exact (hBaseUpper _ _ _ hc hcu).trans hcu
      exact hb.trans (by omega)
  have hOldLarge (keep : List ℕ) (m q : ℕ)
      (hq : q ∈ σ.childPositions) (hqnot : q ∉ keep) :
      (σ.part keep s m).bound ≤ 2*σ.k-4 := by
    let α := σ.part keep s m
    have hNpos := one_le_of_mem_levels hN
    have hNα : N+1 ∈ α.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N,hN,rfl⟩)
    have hNsα : α.sideAt (N+1)=s := (part_sideAt_succ σ keep s m hNpos).trans hNs
    have hMaximum : α.maximumAt (N+1)=σ.maximumAt N := part_maximumAt_succ σ keep s m hNpos
    have hL : q ∈ α.extPositions 1 := by
      rw [part_extPositions_one hpositive]
      exact List.mem_filter.mpr ⟨hq,by simp [hqnot]⟩
    have hSide : α.sideAt 1=s := part_sideAt_one_of_mem hpositive keep s m hL
    have hPosα : ∀ p j v, α.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      have hpl : p<σ.word.length := by
        by_contra h
        have hh := letterAt_of_length_le α
          (show α.word.length≤p by rw [part_word_length]; omega)
        rw [hh] at hp
        cases hp
      cases he : σ.letterAt p with
      | child =>
        rw [part_letterAt_of_child σ keep s m hpl he] at hp
        split at hp
        · cases hp
        · cases hp; omega
      | ext i z =>
        rw [part_letterAt_of_ext σ keep s m hpl he] at hp
        cases hp; omega
    let ν : Context := match α.sideAt (N+1) with
      | Side.lower => {α with u:=min α.u (α.k-α.maximumAt (N+1)), maxima:=α.maxima.take N}
      | Side.upper => {α with a:=min α.a (α.k-α.maximumAt (N+1)), maxima:=α.maxima.take N}
    have hn := ctx_sibling_maximum_upper_normalize α (N+1) hNα
    have hFuel : ∀ fuel, boundFuel fuel α ≤ boundFuel fuel ν := by
      simpa only [Nat.add_sub_cancel] using hn.2.1
    have hFull : α.bound ≤ ν.bound := by simpa only [Nat.add_sub_cancel] using hn.2.2
    have hWord : ν.word=α.word := by cases hs : α.sideAt (N+1) <;> simp only [ν,hs]
    have hMaxima : ν.maxima=α.maxima.take N := by cases hs : α.sideAt (N+1) <;> simp only [ν,hs]
    have hLetter (p : ℕ) : ν.letterAt p=α.letterAt p := by simp only [letterAt,hWord]
    have hChild : ν.childPositions=α.childPositions := by simp only [childPositions,hWord,hLetter]
    have hExt (j : ℕ) : ν.extPositions j=α.extPositions j := by simp only [extPositions,hWord,hLetter]
    have hSides (j : ℕ) : ν.sideAt j=α.sideAt j := by simp only [sideAt,hExt,hLetter]
    have hPosν : ∀ p j v, ν.letterAt p=Letter.ext j v → 1≤j := by
      intro p j v hp
      rw [hLetter] at hp
      exact hPosα p j v hp
    have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1≤j ∧ j≤ρ.maxima.length := by
      simp only [levels,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨i,hi,rfl⟩; omega
      · intro hj; exact ⟨j-1,by omega,by omega⟩
    have hOneν : 1 ∈ ν.levels := by
      apply (hLevelMem ν 1).mpr
      rw [hMaxima,List.length_take]
      have hd : α.maxima.length=σ.maxima.length+1 := by simp [α,part]
      omega
    have hGlobal : (match s with | Side.lower=>ν.u | Side.upper=>ν.a)≤4 := by
      have hc : α.k-α.maximumAt (N+1)≤4 := by
        rw [hMaximum]
        change σ.k-σ.maximumAt N≤4
        omega
      cases s <;> simp only [ν,hNsα]
      all_goals exact (Nat.min_le_right _ _).trans hc
    have hK : ν.k=σ.k := by cases hs : α.sideAt (N+1) <;> simp only [ν,hs] <;> rfl
    have hOpp : (match t with | Side.lower=>ν.u | Side.upper=>ν.a)≤ν.k := by
      cases s <;> cases t
      · exact False.elim (hne rfl)
      · simpa only [ν,hNsα] using hopposite
      · simpa only [ν,hNsα] using hopposite
      · exact False.elim (hne rfl)
    have hb := (ctx_actual_marker_saturated_linear_potential ν hPosν s t hne 1 q
      hOneν (by rw [hSides]; exact hSide) (by rw [hExt]; exact hL)
      (by cases s <;> exact hGlobal) (by cases t <;> exact hOpp) (by rw [hK]; omega)).2
    rw [hK] at hb
    exact hFull.trans hb
  have hCut (keep : List ℕ) (m n p₀ q₀ : ℕ)
      (hp₀ : p₀ ∈ σ.childPositions) (hpkeep : p₀ ∈ keep)
      (hq₀ : q₀ ∈ σ.childPositions) (hqnot : q₀ ∉ keep)
      (hconv : Convex σ keep ∨ Convex σ (σ.childPositions.filter (· ∉ keep)))
      (hm : 1≤m) (hn : 1≤n) (hsum : m+n=σ.k-1) :
      (σ.part keep s m).bound+(σ.part (σ.childPositions.filter (· ∉ keep)) t n).bound≤3*σ.k-8 := by
    let rest := σ.childPositions.filter (· ∉ keep)
    let A := σ.part keep s m
    let B := σ.part rest t n
    have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
      simp only [rest,List.mem_filter,decide_eq_true_eq]
    have hNe (p q : ℕ) (hp : p ∈ keep) (hq : q ∉ keep) : p≠q := by
      intro he; subst q; exact hq hp
    by_cases hQ : ∃ q ∈ active σ, q ∉ keep
    · obtain ⟨q,hqa,hqn⟩ := hQ
      have hqs := (hActive σ q).mp hqa
      have hqRest : q ∈ rest := (hRest q).mpr ⟨hqs.1,hqn⟩
      have hEndpoint
          (he : (∀ p ∈ σ.childPositions, p ∈ keep → ∀ z ∈ σ.childPositions, z ∉ keep → p<z) ∨
            (∀ p ∈ σ.childPositions, p ∈ keep → ∀ z ∈ σ.childPositions, z ∉ keep → z<p)) :
          A.bound+B.bound≤3*σ.k-8 :=
        (ctx_thin_four_rank_top_band_endpoint_cut_bound σ hpositive s t hne
          hclear hopposite hk N hN hNs hmaximum L hthin hwindow keep p₀ q m n hp₀ hpkeep hqs.1 hqn
          hqs.2.1 hqs.2.2 he hm hn hsum).2
      rcases hconv with hconvK | hconvR
      · by_cases hleft : ∃ l ∈ σ.childPositions, l ∉ keep ∧ l<p₀
        · obtain ⟨l,hl,hln,hlp⟩ := hleft
          by_cases hright : ∃ r ∈ σ.childPositions, r ∉ keep ∧ p₀<r
          · obtain ⟨r,hr,hrn,hpr⟩ := hright
            apply (ctx_thin_four_rank_top_band_chosen_internal_cut_bound σ hpositive
              s t hne hclear hk N hN hNs hmaximum L
              (by cases s <;> exact hthin) (by cases s <;> exact hwindow) keep p₀ l r m n
              hp₀ hpkeep hl hr hln hrn ?_ hn).2
            intro p hp hpk
            have ha := hOutside σ keep hconvK p₀ p l hpkeep hpk hl hln
            have hb := hOutside σ keep hconvK p₀ p r hpkeep hpk hr hrn
            omega
          · apply hEndpoint (Or.inr ?_)
            intro p hp hpk z hz hzn
            have hnot : ¬p₀<z := by intro he; exact hright ⟨z,hz,hzn,he⟩
            have hne' := hNe p₀ z hpkeep hzn
            have hh := hOutside σ keep hconvK p₀ p z hpkeep hpk hz hzn
            omega
        · apply hEndpoint (Or.inl ?_)
          intro p hp hpk z hz hzn
          have hnot : ¬z<p₀ := by intro he; exact hleft ⟨z,hz,hzn,he⟩
          have hne' := hNe p₀ z hpkeep hzn
          have hh := hOutside σ keep hconvK p₀ p z hpkeep hpk hz hzn
          omega
      · have hSep : ∀ p ∈ σ.childPositions, p ∈ keep →
            (∀ z ∈ σ.childPositions, z ∉ keep → p<z) ∨
            (∀ z ∈ σ.childPositions, z ∉ keep → z<p) := by
          intro p hp hpk
          have hpn : p ∉ rest := by simp [rest,hpk]
          have hne' := hNe p q hpk hqn
          by_cases hpq : p<q
          · left
            intro z hz hzn
            have hh := hOutside σ rest hconvR q z p hqRest ((hRest z).mpr ⟨hz,hzn⟩) hp hpn
            omega
          · right
            intro z hz hzn
            have hh := hOutside σ rest hconvR q z p hqRest ((hRest z).mpr ⟨hz,hzn⟩) hp hpn
            omega
        by_cases hleft : ∃ l ∈ σ.childPositions, l ∈ keep ∧ l<q
        · obtain ⟨l,hl,hlk,hlq⟩ := hleft
          by_cases hright : ∃ r ∈ σ.childPositions, r ∈ keep ∧ q<r
          · obtain ⟨r,hr,hrk,hqr⟩ := hright
            apply (ctx_thin_four_rank_top_band_opposite_internal_cut_bound σ hpositive
              s t hne hclear hopposite hk N L hN hNs hmaximum hthin hwindow keep q l r m n
              hqs.1 hqn hqs.2.1 hqs.2.2 hl hr hlk hrk ?_ hSep hm hn hsum).2
            intro z hz hzn
            have hzR := (hRest z).mpr ⟨hz,hzn⟩
            have hln : l ∉ rest := by simp [rest,hlk]
            have hrn : r ∉ rest := by simp [rest,hrk]
            have ha := hOutside σ rest hconvR q z l hqRest hzR hl hln
            have hb := hOutside σ rest hconvR q z r hqRest hzR hr hrn
            omega
          · apply hEndpoint (Or.inl ?_)
            intro p hp hpk z hz hzn
            rcases hSep p hp hpk with ha | hb
            · exact ha z hz hzn
            · exact False.elim (hright ⟨p,hp,hpk,hb q hqs.1 hqn⟩)
        · apply hEndpoint (Or.inr ?_)
          intro p hp hpk z hz hzn
          rcases hSep p hp hpk with ha | hb
          · exact False.elim (hleft ⟨p,hp,hpk,ha q hqs.1 hqn⟩)
          · exact hb z hz hzn
    · have hB : B.bound=0 := by
        apply hZero B (hPositivePart σ rest t n)
        intro p hp hcu hca
        have hh := hPartActive σ rest t n p ((hActive B p).mpr ⟨hp,hcu,hca⟩)
        exact hQ ⟨p,hh.1,((hRest p).mp hh.2).2⟩
      have hA := hOldLarge keep m q₀ hq₀ hqnot
      change A.bound+B.bound≤3*σ.k-8
      rw [hB,Nat.add_zero]
      exact hA.trans (by omega)
  have hFuel : ∀ fuel, boundFuel fuel σ≤3*σ.k-8 := by
    intro fuel
    cases fuel with
    | zero => exact Nat.zero_le _
    | succ fuel =>
      rw [boundFuel]
      split
      · exact hBase
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hz
        obtain ⟨keep,hkeep,d,hd,hz⟩ := hz
        have hd' := List.mem_range.mp hd
        obtain ⟨hkl,hkne,hksub⟩ := mem_blocks hkeep
        obtain ⟨p,hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ σ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup σ).subperm h).length_le
          omega
        obtain ⟨q,hq,hqn⟩ := hremoved
        let rest := σ.childPositions.filter (· ∉ keep)
        have hforward (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=σ.k-1) :
            boundFuel fuel (σ.part keep s a)+boundFuel fuel (σ.part rest t b)≤3*σ.k-8 :=
          (Nat.add_le_add (hFuelFull _ fuel) (hFuelFull _ fuel)).trans
            (hCut keep a b p q hp hpk hq hqn (Or.inl (hBlockConvex σ keep hkeep)) ha hb hab)
        have hdouble (v : Side) (c : ℕ) :
            σ.part (σ.childPositions.filter (· ∉ rest)) v c=σ.part keep v c := by
          apply part_congr
          intro r hr
          simp only [rest,List.mem_filter,decide_eq_true_eq,hr,true_and,not_not]
        have hConvDouble : Convex σ (σ.childPositions.filter (· ∉ rest)) := by
          intro a ha b hb z hz haz hzb
          have hac : a ∈ σ.childPositions := (List.mem_filter.mp ha).1
          have hbc : b ∈ σ.childPositions := (List.mem_filter.mp hb).1
          have ha' : a ∈ keep := by
            simpa only [rest,List.mem_filter,decide_eq_true_eq,hac,true_and,not_not] using ha
          have hb' : b ∈ keep := by
            simpa only [rest,List.mem_filter,decide_eq_true_eq,hbc,true_and,not_not] using hb
          have hh := hBlockConvex σ keep hkeep a ha' b hb' z hz haz hzb
          simp only [rest,List.mem_filter,decide_eq_true_eq,hz,true_and,not_not]
          exact hh
        have hbackward (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=σ.k-1) :
            boundFuel fuel (σ.part rest s a)+boundFuel fuel (σ.part keep t b)≤3*σ.k-8 := by
          have hh := hCut rest a b q p hq (by simp [rest,hq,hqn]) hp (by simp [rest,hpk])
            (Or.inr hConvDouble) ha hb hab
          rw [hdouble] at hh
          exact (Nat.add_le_add (hFuelFull _ fuel) (hFuelFull _ fuel)).trans hh
        have hboth (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=σ.k-1) :
            (boundFuel fuel (σ.part keep Side.lower a)+boundFuel fuel (σ.part rest Side.upper b)≤3*σ.k-8) ∧
            (boundFuel fuel (σ.part keep Side.upper b)+boundFuel fuel (σ.part rest Side.lower a)≤3*σ.k-8) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b ha hb hab,by simpa only [Nat.add_comm] using hbackward a b ha hb hab⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a hb ha (by omega),
              hforward b a hb ha (by omega)⟩
          · exact False.elim (hne rfl)
        have hh := hboth (d+1) (σ.k-1-(d+1)) (by omega) (by omega) (by omega)
        rcases hz with rfl | rfl
        · exact hh.1
        · exact hh.2
  exact ⟨hFuel,hFuel _⟩


end ErdosSzekeres
