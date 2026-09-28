import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxThinFourRankNextBandEndpointCutBound
import ESBlueprint.B.CtxThinFourRankNextBandOppositeInternalCutBound
import ESBlueprint.B.CtxThinFourRankNextBandChosenInternalCutBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Prove the full thin four-rank next-band potential3k-9 for every fuel approximation and the full context bound. Positive labels, empty opposite indexed history, opposite global at most k-1, k at least five, an indexed chosen maximum at least k-4, and active pure chosen intervals of width at most two inside a four-rank window are explicit. Both-active cuts use the endpoint, chosen-bracketed active-gap and opposite-internal cut estimates. When one part is inactive, its bound is zero and fuel induction applies to exact original-history pruning of the other part; the old maximum and thin active window are preserved. Chosen global, depth, physical child pattern, inactive children, positive unindexed barriers and other maxima are unrestricted. No actual occurrence at the large old level, recursive-potential or cut-bound premise is assumed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_four_rank_next_band_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (hclear : σ.levelsOn t 0 = [])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1)
  (hk : 5 ≤ σ.k) (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s)
  (hmaximum : σ.k - 4 ≤ σ.maximumAt N) (L : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hwindow : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤ L + 3) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3 * σ.k - 9) ∧ σ.bound ≤ 3 * σ.k - 9 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  let Thin (ρ : Context) := ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p → 0 < ρ.capLimit p p →
    G ρ s-1-ρ.rightExt s 0 p ≤ ρ.leftExt s 0 p+2
  let Window (ρ : Context) := ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p → 0 < ρ.capLimit p p →
    L ≤ ρ.leftExt s 0 p+1 ∧ G ρ s-1-ρ.rightExt s 0 p ≤ L+3
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
  have hBase (ρ : Context) (hthin : Thin ρ) (hk : 5 ≤ ρ.k) : ρ.base≤3*ρ.k-9 := by
    rw [base_eq_baseOf]
    cases he : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ 3*ρ.k-9
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      by_cases hz : ρ.cupLimit p p=0 ∨ ρ.capLimit p p=0
      · simp [baseOf,hz]
      have ht := hthin p hp (by omega) (by omega)
      have hc : (match s with | Side.lower=>ρ.cupLimit p p | Side.upper=>ρ.capLimit p p)≤2 := by
        cases s <;> simp only [Thin,G,cupLimit,capLimit,chainExt] at ht ⊢ <;> omega
      have hcu : ρ.cupLimit p p≤ρ.k-1 := by dsimp only [cupLimit]; omega
      have hca : ρ.capLimit p p≤ρ.k-1 := by dsimp only [capLimit]; omega
      have hb : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k≤ρ.k-1 := by
        cases s
        · exact (hBaseLower _ _ _ hc hca).trans hca
        · exact (hBaseUpper _ _ _ hc hcu).trans hcu
      exact hb.trans (by omega)
  have hGeometric (ρ : Context) (N : ℕ)
      (hpositive : ∀ p j v, ρ.letterAt p=Letter.ext j v → 1≤j)
      (hclear : ρ.levelsOn t 0=[])
      (hopposite : G ρ t≤ρ.k-1) (hk : 5≤ρ.k)
      (hN : N ∈ ρ.levels) (hNs : ρ.sideAt N=s) (hmaximum : ρ.k-4≤ρ.maximumAt N)
      (hthin : Thin ρ) (hwindow : Window ρ)
      (keep : List ℕ) (m n p₀ q₀ : ℕ)
      (hp₀ : p₀ ∈ ρ.childPositions) (hpkeep : p₀ ∈ keep)
      (hpcup : 0 < (ρ.part keep s m).cupLimit p₀ p₀)
      (hpcap : 0 < (ρ.part keep s m).capLimit p₀ p₀)
      (hq₀ : q₀ ∈ ρ.childPositions) (hqnot : q₀ ∉ keep)
      (hqcup : 0 < ρ.cupLimit q₀ q₀) (hqcap : 0 < ρ.capLimit q₀ q₀)
      (hconv : Convex ρ keep ∨ Convex ρ (ρ.childPositions.filter (· ∉ keep)))
      (hm : 1≤m) (hn : 1≤n) (hsum : m+n=ρ.k-1) :
      (ρ.part keep s m).bound+(ρ.part (ρ.childPositions.filter (· ∉ keep)) t n).bound≤3*ρ.k-9 := by
    let rest := ρ.childPositions.filter (· ∉ keep)
    let A := ρ.part keep s m
    let B := ρ.part rest t n
    have hRest (p : ℕ) : p ∈ rest ↔ p ∈ ρ.childPositions ∧ p ∉ keep := by
      simp only [rest,List.mem_filter,decide_eq_true_eq]
    have hNe (p q : ℕ) (hp : p ∈ keep) (hq : q ∉ keep) : p≠q := by
      intro he; subst q; exact hq hp
    have hqActive : q₀ ∈ active ρ := (hActive ρ q₀).mpr ⟨hq₀,hqcup,hqcap⟩
    have hqs := (hActive ρ q₀).mp hqActive
    have hqRest : q₀ ∈ rest := (hRest q₀).mpr ⟨hqs.1,hqnot⟩
    have hEndpoint
        (he : (∀ p ∈ ρ.childPositions, p ∈ keep → ∀ z ∈ ρ.childPositions, z ∉ keep → p<z) ∨
          (∀ p ∈ ρ.childPositions, p ∈ keep → ∀ z ∈ ρ.childPositions, z ∉ keep → z<p)) :
        A.bound+B.bound≤3*ρ.k-9 :=
      (ctx_thin_four_rank_next_band_endpoint_cut_bound ρ hpositive s t hne
        hclear (by cases t <;> exact hopposite) hk L
          (by cases s <;> exact hthin) (by cases s <;> exact hwindow) keep p₀ q₀ m n hp₀ hpkeep hqs.1 hqnot
        hqs.2.1 hqs.2.2 he hm hn hsum).2
    rcases hconv with hconvK | hconvR
    · by_cases hleft : ∃ l ∈ ρ.childPositions, l ∉ keep ∧ l<p₀
      · obtain ⟨l,hl,hln,hlp⟩ := hleft
        by_cases hright : ∃ r ∈ ρ.childPositions, r ∉ keep ∧ p₀<r
        · obtain ⟨r,hr,hrn,hpr⟩ := hright
          apply (ctx_thin_four_rank_next_band_chosen_internal_cut_bound ρ hpositive
            s t hne (by cases t <;> exact hopposite) hk N L hN hNs hmaximum
            (by cases s <;> exact hthin) (by cases s <;> exact hwindow) keep p₀ l r m n
            hp₀ hpkeep hpcup hpcap hl hr hln hrn ?_).2
          intro p hp hpk
          have ha := hOutside ρ keep hconvK p₀ p l hpkeep hpk hl hln
          have hb := hOutside ρ keep hconvK p₀ p r hpkeep hpk hr hrn
          omega
        · apply hEndpoint (Or.inr ?_)
          intro p hp hpk z hz hzn
          have hnot : ¬p₀<z := by intro he; exact hright ⟨z,hz,hzn,he⟩
          have hne' := hNe p₀ z hpkeep hzn
          have hh := hOutside ρ keep hconvK p₀ p z hpkeep hpk hz hzn
          omega
      · apply hEndpoint (Or.inl ?_)
        intro p hp hpk z hz hzn
        have hnot : ¬z<p₀ := by intro he; exact hleft ⟨z,hz,hzn,he⟩
        have hne' := hNe p₀ z hpkeep hzn
        have hh := hOutside ρ keep hconvK p₀ p z hpkeep hpk hz hzn
        omega
    · have hSep : ∀ p ∈ ρ.childPositions, p ∈ keep →
          (∀ z ∈ ρ.childPositions, z ∉ keep → p<z) ∨
          (∀ z ∈ ρ.childPositions, z ∉ keep → z<p) := by
        intro p hp hpk
        have hpn : p ∉ rest := by simp [rest,hpk]
        have hne' := hNe p q₀ hpk hqnot
        by_cases hpq : p<q₀
        · left
          intro z hz hzn
          have hh := hOutside ρ rest hconvR q₀ z p hqRest ((hRest z).mpr ⟨hz,hzn⟩) hp hpn
          omega
        · right
          intro z hz hzn
          have hh := hOutside ρ rest hconvR q₀ z p hqRest ((hRest z).mpr ⟨hz,hzn⟩) hp hpn
          omega
      by_cases hleft : ∃ l ∈ ρ.childPositions, l ∈ keep ∧ l<q₀
      · obtain ⟨l,hl,hlk,hlq⟩ := hleft
        by_cases hright : ∃ r ∈ ρ.childPositions, r ∈ keep ∧ q₀<r
        · obtain ⟨r,hr,hrk,hqr⟩ := hright
          apply (ctx_thin_four_rank_next_band_opposite_internal_cut_bound ρ hpositive
            s t hne (by cases t <;> exact hopposite) hk N L hN hNs hmaximum
            (by cases s <;> exact hthin) (by cases s <;> exact hwindow) keep q₀ l r m n
            hqs.1 hqnot hqs.2.1 hqs.2.2 hl hr hlk hrk ?_ hSep).2
          intro z hz hzn
          have hzR := (hRest z).mpr ⟨hz,hzn⟩
          have hln : l ∉ rest := by simp [rest,hlk]
          have hrn : r ∉ rest := by simp [rest,hrk]
          have ha := hOutside ρ rest hconvR q₀ z l hqRest hzR hl hln
          have hb := hOutside ρ rest hconvR q₀ z r hqRest hzR hr hrn
          omega
        · apply hEndpoint (Or.inl ?_)
          intro p hp hpk z hz hzn
          rcases hSep p hp hpk with ha | hb
          · exact ha z hz hzn
          · exact False.elim (hright ⟨p,hp,hpk,hb q₀ hqs.1 hqnot⟩)
      · apply hEndpoint (Or.inr ?_)
        intro p hp hpk z hz hzn
        rcases hSep p hp hpk with ha | hb
        · exact False.elim (hleft ⟨p,hp,hpk,ha q₀ hqs.1 hqnot⟩)
        · exact hb z hz hzn
  have hFuel : ∀ (fuel : ℕ) (ρ : Context) (N : ℕ),
      (∀ p j v, ρ.letterAt p=Letter.ext j v → 1≤j) → ρ.levelsOn t 0=[] →
      G ρ t≤ρ.k-1 → 5≤ρ.k → N ∈ ρ.levels → ρ.sideAt N=s → ρ.k-4≤ρ.maximumAt N →
      Thin ρ → Window ρ → boundFuel fuel ρ≤3*ρ.k-9 := by
    intro fuel
    induction fuel with
    | zero => intro ρ N _ _ _ _ _ _ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ N hpositive hclear hopposite hk hN hNs hmaximum hthin hwindow
      have hPruned (ks : List ℕ) (v : Side) (M : ℕ) :
          boundFuel fuel (ρ.part ks v M) ≤ 3*ρ.k-9 := by
        let τ : Context := {ρ with
          word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
            | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length+1) v
            | Letter.ext j w => Letter.ext j w) }
        have hh := ctx_part_pruning_history_transport ρ hpositive ks v M
        change (∀ p j w, τ.letterAt p=Letter.ext j w → 1≤j) ∧
          τ.childPositions=ρ.childPositions.filter (· ∈ ks) ∧
          (∀ j ∈ ρ.levels, τ.extPositions j=ρ.extPositions j ∧ τ.sideAt j=ρ.sideAt j) ∧
          (∀ w top, τ.levelsOn w top=ρ.levelsOn w top) ∧
          (∀ w top p, τ.leftExt w top p=ρ.leftExt w top p ∧
            τ.rightExt w top p=ρ.rightExt w top p) ∧
          (∀ p q, τ.cupLimit p q=ρ.cupLimit p q ∧ τ.capLimit p q=ρ.capLimit p q) ∧
          active τ=(active ρ).filter (· ∈ ks) ∧
          (∀ f, boundFuel f (ρ.part ks v M)≤boundFuel f τ) ∧ (ρ.part ks v M).bound≤τ.bound at hh
        obtain ⟨hτPos,hτChild,hτHist,hτLevels,hτExt,hτLimits,hτActive,hToτ,_⟩ := hh
        have hSource (p : ℕ) (hp : p ∈ active τ) : p ∈ active ρ := by
          rw [hτActive] at hp
          exact (Finset.mem_filter.mp hp).1
        have hτThin : Thin τ := by
          intro p hp hc hu
          have hs := (hActive ρ p).mp (hSource p ((hActive τ p).mpr ⟨hp,hc,hu⟩))
          change G ρ s-1-τ.rightExt s 0 p ≤ τ.leftExt s 0 p+2
          rw [(hτExt s 0 p).1,(hτExt s 0 p).2]
          exact hthin p hs.1 hs.2.1 hs.2.2
        have hτWindow : Window τ := by
          intro p hp hc hu
          have hs := (hActive ρ p).mp (hSource p ((hActive τ p).mpr ⟨hp,hc,hu⟩))
          change L≤τ.leftExt s 0 p+1 ∧ G ρ s-1-τ.rightExt s 0 p≤L+3
          rw [(hτExt s 0 p).1,(hτExt s 0 p).2]
          exact hwindow p hs.1 hs.2.1 hs.2.2
        exact (hToτ fuel).trans (ih τ N hτPos ((hτLevels t 0).trans hclear) hopposite hk hN
          ((hτHist N hN).2.trans hNs) hmaximum hτThin hτWindow)
      have hCut (keep : List ℕ) (m n p₀ q₀ : ℕ)
          (hp₀ : p₀ ∈ ρ.childPositions) (hpkeep : p₀ ∈ keep)
          (hq₀ : q₀ ∈ ρ.childPositions) (hqnot : q₀ ∉ keep)
          (hconv : Convex ρ keep ∨ Convex ρ (ρ.childPositions.filter (· ∉ keep)))
          (hm : 1≤m) (hn : 1≤n) (hsum : m+n=ρ.k-1) :
          boundFuel fuel (ρ.part keep s m)+
            boundFuel fuel (ρ.part (ρ.childPositions.filter (· ∉ keep)) t n)≤3*ρ.k-9 := by
        let rest := ρ.childPositions.filter (· ∉ keep)
        let A := ρ.part keep s m
        let B := ρ.part rest t n
        by_cases hA : (active A).Nonempty
        · by_cases hB : (active B).Nonempty
          · obtain ⟨p,hp⟩ := hA
            obtain ⟨q,hq⟩ := hB
            have hpA := (hActive A p).mp hp
            have hpS := hPartActive ρ keep s m p hp
            have hps := (hActive ρ p).mp hpS.1
            have hqS := hPartActive ρ rest t n q hq
            have hqs := (hActive ρ q).mp hqS.1
            have hqn : q∉keep := of_decide_eq_true (List.mem_filter.mp hqS.2).2
            have hc := hGeometric ρ N hpositive hclear hopposite hk hN hNs hmaximum hthin hwindow
              keep m n p q hps.1 hpS.2 hpA.2.1 hpA.2.2 hqs.1 hqn hqs.2.1 hqs.2.2 hconv hm hn hsum
            exact (Nat.add_le_add (hFuelFull A fuel) (hFuelFull B fuel)).trans hc
          · have hz : B.bound=0 := hZero B (hPositivePart ρ rest t n) (by
              intro q hq hc hu
              exact hB ⟨q,(hActive B q).mpr ⟨hq,hc,hu⟩⟩)
            have hf := hFuelFull B fuel
            have ha : boundFuel fuel A ≤ 3*ρ.k-9 := hPruned keep s m
            change boundFuel fuel A+boundFuel fuel B≤3*ρ.k-9
            omega
        · have hz : A.bound=0 := hZero A (hPositivePart ρ keep s m) (by
            intro p hp hc hu
            exact hA ⟨p,(hActive A p).mpr ⟨hp,hc,hu⟩⟩)
          have hf := hFuelFull A fuel
          have hb : boundFuel fuel B ≤ 3*ρ.k-9 := hPruned rest t n
          change boundFuel fuel A+boundFuel fuel B≤3*ρ.k-9
          omega
      rw [boundFuel]
      split
      · exact hBase ρ hthin hk
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hz
        obtain ⟨keep,hkeep,d,hd,hz⟩ := hz
        have hd' := List.mem_range.mp hd
        obtain ⟨hkl,hkne,hksub⟩ := mem_blocks hkeep
        obtain ⟨p,hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ ρ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ ρ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup ρ).subperm h).length_le
          omega
        obtain ⟨q,hq,hqn⟩ := hremoved
        let rest := ρ.childPositions.filter (· ∉ keep)
        have hforward (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=ρ.k-1) :
            boundFuel fuel (ρ.part keep s a)+boundFuel fuel (ρ.part rest t b)≤3*ρ.k-9 :=
          hCut keep a b p q hp hpk hq hqn (Or.inl (hBlockConvex ρ keep hkeep)) ha hb hab
        have hdouble (v : Side) (c : ℕ) :
            ρ.part (ρ.childPositions.filter (· ∉ rest)) v c=ρ.part keep v c := by
          apply part_congr
          intro r hr
          simp only [rest,List.mem_filter,decide_eq_true_eq,hr,true_and,not_not]
        have hConvDouble : Convex ρ (ρ.childPositions.filter (· ∉ rest)) := by
          intro a ha b hb z hz haz hzb
          have hac : a ∈ ρ.childPositions := (List.mem_filter.mp ha).1
          have hbc : b ∈ ρ.childPositions := (List.mem_filter.mp hb).1
          have ha' : a ∈ keep := by
            simpa only [rest,List.mem_filter,decide_eq_true_eq,hac,true_and,not_not] using ha
          have hb' : b ∈ keep := by
            simpa only [rest,List.mem_filter,decide_eq_true_eq,hbc,true_and,not_not] using hb
          have hh := hBlockConvex ρ keep hkeep a ha' b hb' z hz haz hzb
          simp only [rest,List.mem_filter,decide_eq_true_eq,hz,true_and,not_not]
          exact hh
        have hbackward (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=ρ.k-1) :
            boundFuel fuel (ρ.part rest s a)+boundFuel fuel (ρ.part keep t b)≤3*ρ.k-9 := by
          have hh := hCut rest a b q p hq (by simp [rest,hq,hqn]) hp (by simp [rest,hpk])
            (Or.inr hConvDouble) ha hb hab
          rw [hdouble] at hh
          exact hh
        have hboth (a b : ℕ) (ha : 1≤a) (hb : 1≤b) (hab : a+b=ρ.k-1) :
            (boundFuel fuel (ρ.part keep Side.lower a)+boundFuel fuel (ρ.part rest Side.upper b)≤3*ρ.k-9) ∧
            (boundFuel fuel (ρ.part keep Side.upper b)+boundFuel fuel (ρ.part rest Side.lower a)≤3*ρ.k-9) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b ha hb hab,by simpa only [Nat.add_comm] using hbackward a b ha hb hab⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a hb ha (by omega),
              hforward b a hb ha (by omega)⟩
          · exact False.elim (hne rfl)
        have hh := hboth (d+1) (ρ.k-1-(d+1)) (by omega) (by omega) (by omega)
        rcases hz with rfl | rfl
        · exact hh.1
        · exact hh.2
  have hThinσ : Thin σ := by cases s <;> exact hthin
  have hWindowσ : Window σ := by cases s <;> exact hwindow
  have hAll := fun f => hFuel f σ N hpositive hclear (by cases t <;> exact hopposite) hk hN hNs hmaximum hThinσ hWindowσ
  exact ⟨hAll,hAll _⟩


end ErdosSzekeres
