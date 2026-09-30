import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxSingleRunDescendantBoundNormalize
import ESBlueprint.B.CtxPointLimitsEqOfChildInterval
import Init.Data.List.Nat.Erase

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- Bridge from the root form of run contraction (C1r, hypothesis hroot) to run contraction in every part of a well-formed single-run context (C1p): by ctx_single_run_descendant_bound_normalize the part and its contraction have the bounds of the normalized one-level contexts with (a, u) = (capLimit + 1, cupLimit + 1) of the run (the same for both, since all children of a single run have equal point limits); the older letters are inert there and lie outside the child span, so deleting them leaves the bound unchanged, which gives a word over child and level-one letters of one side, where hroot applies. No proof of hroot is asserted (R7/R10, runs/claude-comb-closedform-20260930).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_single_run_descendant_bound_normalize
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_part_run_contraction_of_one_level_root (hroot : ∀ (a u k m : ℕ), 3 ≤ k → 1 ≤ a → a ≤ k → 1 ≤ u → u ≤ k → 1 ≤ m → m ≤ k - 2 → ∀ (side : Ctx.Side) (left right : List Ctx.Letter), (∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) → ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound = ({ a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] } : Ctx.Context).bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (s : Ctx.Side) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ σ.k - 2) (left right : List Ctx.Letter) (hword : (σ.part keep s m).word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) : (σ.part keep s m).bound = ({ σ.part keep s m with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound := by
  classical
  let up (p i : ℕ) := if i < p then i else i + 1
  have hup : ∀ p, StrictMono (up p) := by
    intro p i j hij
    dsimp [up]
    split_ifs <;> omega
  have hRange : ∀ n p, p ≤ n →
      (List.range (n + 1)).filter (fun i ↦ i ≠ p) = (List.range n).map (up p) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      have : p = 0 := by omega
      subst p
      simp
    | succ n ih =>
      intro p hp
      by_cases hpn : p = n + 1
      · subst p
        have hpre : (List.range (n + 1)).map (up (n + 1)) = List.range (n + 1) := by
          calc
            _ = (List.range (n + 1)).map (fun i ↦ i) := by
              apply List.map_congr_left
              intro i hi
              simp [up, List.mem_range.1 hi]
            _ = _ := List.map_id' _
        rw [List.range_succ, List.filter_append]
        have hself : (List.range (n + 1)).filter (fun i ↦ i ≠ n + 1) =
            List.range (n + 1) := by
          apply List.filter_eq_self.2
          intro i hi
          simp only [decide_eq_true_eq]
          exact Nat.ne_of_lt (List.mem_range.1 hi)
        rw [hself, hpre]
        simp
      · have hpn' : p ≤ n := by omega
        rw [List.range_succ, List.filter_append, ih p hpn', List.range_succ,
          List.map_append]
        have hnp : n + 1 ≠ p := by omega
        have hnp' : ¬ n < p := by omega
        simp [up, hnp, hnp']
  have hFilter : ∀ n p (P Q : ℕ → Bool), p ≤ n → P p = false →
      (∀ i, i < n → P (up p i) = Q i) →
      (List.range (n + 1)).filter P = ((List.range n).filter Q).map (up p) := by
    intro n p P Q hp hfalse hletter
    have hremove : (List.range (n + 1)).filter P =
        ((List.range (n + 1)).filter (fun i ↦ i ≠ p)).filter P := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro i hi
      by_cases hip : i = p
      · subst i; simp [hfalse]
      · simp [hip]
    rw [hremove, hRange n p hp, List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    exact hletter i (List.mem_range.1 hi)
  have hGeometry : ∀ (big small : Context) p level s,
      big.maxima = small.maxima → small.maxima.length < level →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.childPositions = small.childPositions.map (up p) ∧
      (∀ N ∈ small.levels, big.extPositions N = (small.extPositions N).map (up p)) ∧
      (∀ N ∈ small.levels, big.sideAt N = small.sideAt N) := by
    intro big small p level s hm hlevel hlen hp hbp hletter
    have hchildren : big.childPositions = small.childPositions.map (up p) := by
      unfold childPositions
      rw [hlen]
      apply hFilter _ p _ _ hp
      · simp [hbp]
      · intro i hi; rw [hletter i hi]
    have hexternals : ∀ N ∈ small.levels,
        big.extPositions N = (small.extPositions N).map (up p) := by
      intro N hN
      have hNle : N ≤ small.maxima.length := by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hN
        have := List.mem_range.1 hj
        omega
      have hne : level ≠ N := by omega
      unfold extPositions
      rw [hlen]
      apply hFilter _ p _ _ hp
      · simp [hbp, hne]
      · intro i hi; rw [hletter i hi]
    refine ⟨hchildren, hexternals, ?_⟩
    intro N hN
    unfold sideAt
    rw [hexternals N hN, List.head?_map]
    cases hh : (small.extPositions N).head? with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      have hqn : q < small.word.length :=
        List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_head? hh)).1
      rw [hletter q hqn]
  have hFolds : ∀ (big small : Context) p,
      (∀ N ∈ small.levels, big.extPositions N = (small.extPositions N).map (up p)) →
      ∀ (ls : List ℕ), (∀ N ∈ ls, N ∈ small.levels) → ∀ e c,
      (ls.foldl (leftStep big) (up p e, c)).2 =
          (ls.foldl (leftStep small) (e, c)).2 ∧
      (ls.foldl (rightStep big) (up p e, c)).2 =
          (ls.foldl (rightStep small) (e, c)).2 := by
    intro big small p hext ls
    induction ls with
    | nil => intros; exact ⟨rfl, rfl⟩
    | cons N ls ih =>
      intro hlevels e c
      have hrest := fun j hj ↦ hlevels j (List.mem_cons_of_mem N hj)
      have hleft : ((big.extPositions N).filter (· < up p e)).getLast? =
          (((small.extPositions N).filter (· < e)).getLast?).map (up p) := by
        rw [hext N (hlevels N (List.mem_cons_self ..)), List.filter_map]
        have hf : (fun i ↦ decide (up p i < up p e)) = (fun i ↦ decide (i < e)) := by
          funext i
          simp only [(hup p).lt_iff_lt]
        simp only [Function.comp_def]
        rw [hf, List.getLast?_map]
      have hright : ((big.extPositions N).filter (up p e < ·)).head? =
          (((small.extPositions N).filter (e < ·)).head?).map (up p) := by
        rw [hext N (hlevels N (List.mem_cons_self ..)), List.filter_map]
        have hf : (fun i ↦ decide (up p e < up p i)) = (fun i ↦ decide (e < i)) := by
          funext i
          simp only [(hup p).lt_iff_lt]
        simp only [Function.comp_def]
        rw [hf, List.head?_map]
      constructor
      · simp only [List.foldl_cons, leftStep]
        rw [hleft]
        cases hq : ((small.extPositions N).filter (· < e)).getLast? with
        | none => simp only [Option.map_none]; exact (ih hrest e c).1
        | some q => simp only [Option.map_some]; exact (ih hrest q (c + 1)).1
      · simp only [List.foldl_cons, rightStep]
        rw [hright]
        cases hq : ((small.extPositions N).filter (e < ·)).head? with
        | none => simp only [Option.map_none]; exact (ih hrest e c).2
        | some q => simp only [Option.map_some]; exact (ih hrest q (c + 1)).2
  have hBase : ∀ (big small : Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      small.maxima.length < level →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.base = small.base := by
    intro big small p level s ha hu hk hm hlevel hlen hp hbp hletter
    obtain ⟨hchildren, hexternals, hsides⟩ :=
      hGeometry big small p level s hm hlevel hlen hp hbp hletter
    have hlevels : ∀ s top, big.levelsOn s top = small.levelsOn s top := by
      intro t top
      unfold levelsOn levels
      rw [hm]
      apply List.filter_congr
      intro N hN
      rw [hsides N hN]
    have hExt : ∀ s top e,
        big.leftExt s top (up p e) = small.leftExt s top e ∧
        big.rightExt s top (up p e) = small.rightExt s top e := by
      intro t top e
      have hmap : ∀ ls ∈ (small.levelsOn t top).sublists,
          (ls.foldl (leftStep big) (up p e, 0)).2 =
            (ls.foldl (leftStep small) (e, 0)).2 ∧
          (ls.foldl (rightStep big) (up p e, 0)).2 =
            (ls.foldl (rightStep small) (e, 0)).2 := by
        intro ls hls
        apply hFolds big small p hexternals ls
        intro N hN
        exact (List.mem_filter.1 ((List.mem_sublists.1 hls).subset hN)).1
      constructor
      · rw [leftExt_eq, leftExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).1)
      · rw [rightExt_eq, rightExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).2)
    have hchain : ∀ s e,
        big.chainExt s (up p e) (up p e) = small.chainExt s e e := by
      intro t e
      unfold chainExt
      rw [(hExt t 0 e).1, (hExt t 0 e).2]
    have hjoin : ∀ s e,
        big.joinExt s (up p e) (up p e) = small.joinExt s e e := by
      intro t e
      unfold joinExt
      rw [hchain t e, hlevels]
      congr 3
      apply List.map_congr_left
      intro N hN
      rw [(hExt t N e).1, (hExt t N e).2]
      simp [maximumAt, hm]
    unfold base
    rw [hchildren, List.head?_map]
    cases hh : small.childPositions.head? with
    | none => rfl
    | some e =>
      simp only [Option.map_some]
      have hcl : big.cupLimit (up p e) (up p e) = small.cupLimit e e := by
        unfold cupLimit
        rw [hu, hk, hchain, hjoin]
      have hpl : big.capLimit (up p e) (up p e) = small.capLimit e e := by
        unfold capLimit
        rw [ha, hk, hchain, hjoin]
      rw [hcl, hpl, hk]
  have hMapMem : ∀ p (A : List ℕ) i, up p i ∈ A.map (up p) ↔ i ∈ A := by
    intro p A i
    constructor
    · intro h
      obtain ⟨j, hj, heq⟩ := List.mem_map.1 h
      have hji := (hup p).injective heq
      simpa [hji] using hj
    · exact List.mem_map_of_mem
  have hRest : ∀ p (A B : List ℕ),
      (A.map (up p)).filter (fun i ↦ i ∉ B.map (up p)) =
        (A.filter (fun i ↦ i ∉ B)).map (up p) := by
    intro p A B
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    change decide (up p i ∉ B.map (up p)) = decide (i ∉ B)
    simp only [hMapMem]
  have hBlocks : ∀ (big small : Context) p,
      big.childPositions = small.childPositions.map (up p) →
      big.blocks = small.blocks.map (fun B ↦ B.map (up p)) := by
    intro big small p hc
    simp only [blocks, hc, List.length_map]
    have hraw : ((List.range small.childPositions.length).flatMap fun i ↦
          (List.range (small.childPositions.length - i)).map fun len ↦
            ((small.childPositions.map (up p)).drop i).take (len + 1)) =
        ((List.range small.childPositions.length).flatMap fun i ↦
          (List.range (small.childPositions.length - i)).map fun len ↦
            (small.childPositions.drop i).take (len + 1)).map (fun B ↦ B.map (up p)) := by
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro i hi
      rw [List.map_map]
      apply List.map_congr_left
      intro len hlen
      simp [List.map_take, List.map_drop]
    rw [hraw, List.filter_map]
    congr 1
    apply List.filter_congr
    intro B hB
    simp
  have hRuns : ∀ (big small : Context) p level s,
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      (p = 0 ∨ p = small.word.length) → big.numRuns = small.numRuns := by
    intro big small p level s hlen hp hbp hletter hedge
    unfold numRuns
    rw [hlen]
    have hfilter := hFilter small.word.length p
      (fun i ↦ decide (big.letterAt i = Letter.child ∧
        (i = 0 ∨ big.letterAt (i - 1) ≠ Letter.child)))
      (fun i ↦ decide (small.letterAt i = Letter.child ∧
        (i = 0 ∨ small.letterAt (i - 1) ≠ Letter.child))) hp (by simp [hbp])
    have hmap : ∀ i, i < small.word.length →
        decide (big.letterAt (up p i) = Letter.child ∧
          (up p i = 0 ∨ big.letterAt (up p i - 1) ≠ Letter.child)) =
        decide (small.letterAt i = Letter.child ∧
          (i = 0 ∨ small.letterAt (i - 1) ≠ Letter.child)) := by
      intro i hi
      rw [hletter i hi]
      rcases hedge with rfl | rfl
      · have hu : up 0 i = i + 1 := by simp [up]
        rw [hu]
        by_cases hi0 : i = 0
        · subst i
          simp [hbp]
        · have hip : i - 1 < small.word.length := by omega
          have huprev : up 0 (i - 1) = i := by simp [up]; omega
          rw [show i + 1 - 1 = up 0 (i - 1) by omega, hletter _ hip]
          simp [hi0]
      · have hu : up small.word.length i = i := by simp [up, hi]
        rw [hu]
        by_cases hi0 : i = 0
        · simp [hi0]
        · have hip : i - 1 < small.word.length := by omega
          have huprev : up small.word.length (i - 1) = i - 1 := by simp [up, hip]
          conv_lhs => rw [← huprev, hletter _ hip]
    rw [hfilter hmap, List.length_map]
  have hFuel : ∀ fuel (big small : Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      small.maxima.length < level →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      (p = 0 ∨ p = small.word.length) →
      boundFuel fuel big = boundFuel fuel small := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro big small p level s ha hu hk hm hlevel hlen hp hbp hletter hedge
      obtain ⟨hc, hext, hsides⟩ :=
        hGeometry big small p level s hm hlevel hlen hp hbp hletter
      have hparts : ∀ (B : List ℕ) (t : Side) m,
          boundFuel fuel (big.part (B.map (up p)) t m) =
            boundFuel fuel (small.part B t m) := by
        intro B t m
        have hpbig : p < big.word.length := by omega
        apply ih (big.part (B.map (up p)) t m) (small.part B t m) p (level + 1) s
        · exact ha
        · exact hu
        · exact hk
        · simp only [part_maxima, hm]
        · simp only [part_maxima, List.length_cons]
          omega
        · simpa only [part_word_length] using hlen
        · simpa only [part_word_length] using hp
        · exact part_letterAt_of_ext big (B.map (up p)) t m hpbig hbp
        · intro i hi
          have his : i < small.word.length := by simpa only [part_word_length] using hi
          have hib : up p i < big.word.length := by
            rw [hlen]
            dsimp [up]
            split_ifs <;> omega
          cases hs : small.letterAt i with
          | child =>
            rw [part_letterAt_of_child big (B.map (up p)) t m hib
              ((hletter i his).trans hs), part_letterAt_of_child small B t m his hs]
            simp only [hMapMem]
          | ext N t' =>
            rw [part_letterAt_of_ext big (B.map (up p)) t m hib
              ((hletter i his).trans hs), part_letterAt_of_ext small B t m his hs]
        · simpa only [part_word_length] using hedge
      have hruns := hRuns big small p level s hlen hp hbp hletter hedge
      simp only [boundFuel, hruns]
      split_ifs with hr
      · exact hBase big small p level s ha hu hk hm hlevel hlen hp hbp hletter
      · rw [hc, hBlocks big small p hc, hk, List.flatMap_map]
        apply congrArg (fun xs : List ℕ ↦ (xs.max?).getD 0)
        apply List.flatMap_congr
        intro B hB
        rw [hRest]
        apply List.flatMap_congr
        intro d hd
        simp only [hparts]
  have hCtxEq : ∀ (τ ρ : Context), τ.a = ρ.a → τ.u = ρ.u → τ.k = ρ.k →
      τ.word = ρ.word → τ.maxima = ρ.maxima → τ = ρ := by
    intro τ ρ ha hu hk hw hm
    cases τ
    cases ρ
    cases ha
    cases hu
    cases hk
    cases hw
    cases hm
    rfl
  have hInterval (ρ : Context) (hruns : ρ.numRuns ≤ 1) (hchildNe : ρ.childPositions ≠ []) :
      ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ ρ.childPositions := by
      rw [hcons]
      exact List.mem_cons_self
    have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
    have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range ρ.word.length).filter fun p ↦
      ρ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hstartsLen : starts.length ≤ 1 := by
      simpa [starts, Ctx.Context.numRuns] using hruns
    have hstartsNodup : starts.Nodup := by
      exact List.nodup_range.filter _
    have hbRange : b < ρ.word.length := by
      exact List.mem_range.1 (List.mem_filter.1 hb).1
    have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition :
        b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro hprev
        have hprevMem : b - 1 ∈ ρ.childPositions := by
          apply List.mem_filter.2
          exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
        have := hmin (b - 1) hprevMem
        omega
    have hbStart : b ∈ starts := by
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hbRange, hbLetter, hbStartCondition⟩
    have hstartUnique : ∀ p ∈ starts, p = b := by
      intro p hp
      by_contra hpb
      have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact List.mem_toFinset.2 hbStart
        · exact List.mem_toFinset.2 hp
      have hcard := Finset.card_le_card hsubset
      rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
      have htwo : ({b, p} : Finset ℕ).card = 2 := by
        simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
      intro p hp hpb
      have hpRange : p < ρ.word.length :=
        List.mem_range.1 (List.mem_filter.1 hp).1
      have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by
        have := hmin p hp
        omega
      by_contra hprevMem
      have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
        intro hletter
        apply hprevMem
        apply List.mem_filter.2
        exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
      have hpStart : p ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
      exact hpb (hstartUnique p hpStart)
    have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
        q ∈ ρ.childPositions := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hp q hbq hqp
        by_cases hpb : p = b
        · have : q = b := by omega
          simpa [this] using hb
        by_cases hqp' : q = p
        · simpa [hqp'] using hp
        exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
    let e := ρ.childPositions.getLast hchildNe
    have he : e ∈ ρ.childPositions := by
      dsimp [e]
      exact List.getLast_mem _
    have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
      intro p hp
      simpa [e] using hordered.rel_getLast hp
    have hbe : b ≤ e := hmin e he
    have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
        p ∈ List.range' b (e + 1 - b) := by
      intro p
      simp only [List.mem_range'_1]
      constructor
      · intro hp
        exact ⟨hmin p hp, by have := hmax p hp; omega⟩
      · rintro ⟨hbp, hp⟩
        exact hfill e he p hbp (by omega)
    have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
      (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
        List.nodup_range').2 hmemRange
    have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
      List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
    have hlen : ρ.childPositions.length = e + 1 - b := by
      rw [hrange]
      simp
    have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
      rw [hlen]
      exact hrange
    exact ⟨b, hinterval⟩
  have hPositions : ∀ (τ : Context) (L R : List Letter) (n : ℕ),
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate n Letter.child ++ R →
      τ.childPositions = List.range' L.length n := by
    intro τ L R n hext hw
    apply (childPositions_pairwise τ).eq_of_mem_iff (List.pairwise_lt_range' _ (by omega))
    intro p
    simp only [Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_range'_1]
    have hsize : τ.word.length = L.length + n + R.length := by simp [hw, Nat.add_assoc]
    by_cases hpL : p < L.length
    · have hn : τ.letterAt p ≠ Letter.child := by
        have hx := hext L[p] (List.mem_append_left _ (List.getElem_mem hpL))
        simpa [Context.letterAt, hw, List.append_assoc, List.getElem?_append_left hpL,
          List.getElem?_eq_getElem hpL] using hx
      constructor
      · rintro ⟨_, h⟩; exact (hn h).elim
      · omega
    · by_cases hpN : p < L.length + n
      · have hrel : p - L.length < n := by omega
        have hp : p < τ.word.length := by omega
        have hs : τ.letterAt p = Letter.child := by
          simp [Context.letterAt, hw, List.append_assoc,
            List.getElem?_append_right (Nat.le_of_not_gt hpL),
            List.getElem?_append_left (show p - L.length <
              (List.replicate n Letter.child).length by simpa using hrel), hrel]
        exact ⟨fun _ ↦ ⟨by omega, hpN⟩, fun _ ↦ ⟨hp, hs⟩⟩
      · constructor
        · rintro ⟨hp, hs⟩
          have hrel : p - L.length - n < R.length := by omega
          have hx := hext R[p - L.length - n]
            (List.mem_append_right _ (List.getElem_mem hrel))
          have he : τ.letterAt p = R[p - L.length - n] := by
            simp [Context.letterAt, hw, List.append_assoc,
              List.getElem?_append_right (Nat.le_of_not_gt hpL),
              List.getElem?_append_right (show (List.replicate n Letter.child).length ≤
                p - L.length by simp; omega), List.getElem?_eq_getElem hrel]
          exact (hx (he.symm.trans hs)).elim
        · omega
  have hRunCount : ∀ (τ : Context) (a n : ℕ),
      τ.childPositions = List.range' a n → τ.numRuns ≤ 1 := by
    intro τ a n hps
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by simpa [starts] using hp
      have hp' : a ≤ p ∧ p < a + n := by
        have hm : p ∈ τ.childPositions := by simp [Context.childPositions, hstart]
        simpa [hps, List.mem_range'_1] using hm
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := by rw [hps, List.mem_range'_1]; omega
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    exact hruns
  let shift : Letter → Letter
    | .child => .child
    | .ext N s => .ext (N + 1) s
  let replace (keep : List ℕ) (s : Side) (p : ℕ) : Letter → Letter
    | .child => if p ∈ keep then .child else .ext 1 s
    | .ext N t => .ext (N + 1) t
  have hPartMap : ∀ (τ : Context) keep s n,
      (τ.part keep s n).word = τ.word.mapIdx (replace keep s) := by
    intro τ keep s n
    apply List.ext_getElem (by simp [Context.part])
    intro i hi hj
    simp only [Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hi' : i < τ.word.length := by simpa [Context.part] using hi
    simp [Context.letterAt, List.getElem?_eq_getElem hi', replace]
    rfl
  have hMapExt : ∀ (L : List Letter) keep s off,
      (∀ x ∈ L, x ≠ Letter.child) →
      L.mapIdx (fun i x ↦ replace keep s (i + off) x) = L.map shift := by
    intro L keep s off hL
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hi' : i < L.length := by simpa using hi
    have hx := hL L[i] (List.getElem_mem hi')
    simp only [List.getElem_mapIdx, List.getElem_map]
    cases he : L[i] with
    | child => exact (hx he).elim
    | ext N t => simp [replace, shift]
  have hReconstruct : ∀ (τ : Context) (b n : ℕ), 0 < n →
      τ.childPositions = List.range' b n →
      ∃ L R : List Letter, L.length = b ∧
        τ.word = L ++ List.replicate n Letter.child ++ R ∧
        (∀ x ∈ L ++ R, x ≠ Letter.child) := by
    intro τ b n hn hp
    have hmem : ∀ p, p ∈ τ.childPositions ↔ b ≤ p ∧ p < b + n := by
      intro p
      rw [hp, List.mem_range'_1]
    have hlen : b + n ≤ τ.word.length := by
      have hh : b + n - 1 ∈ τ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
      have := List.mem_range.mp (List.mem_filter.mp hh).1
      omega
    let L := τ.word.take b
    let R := τ.word.drop (b + n)
    have hLlen : L.length = b := by
      simp [L, Nat.min_eq_left (show b ≤ τ.word.length by omega)]
    have hmid : (τ.word.drop b).take n = List.replicate n Letter.child := by
      apply List.ext_getElem (by simp; omega)
      intro i hi hj
      have hi' : i < n := by simpa using hj
      have hib : b + i < τ.word.length := by omega
      have hchild : b + i ∈ τ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
      have hc : τ.letterAt (b + i) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hchild).2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_replicate]
      simpa [Context.letterAt, List.getElem?_eq_getElem hib] using hc
    have hw : τ.word = L ++ List.replicate n Letter.child ++ R := by
      rw [← hmid]
      dsimp [L, R]
      rw [← List.take_add, List.take_append_drop]
    refine ⟨L, R, hLlen, hw, ?_⟩
    intro x hx hc
    subst x
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hib : i < b := by simpa [hLlen] using hi
      have hiw : i < τ.word.length := by omega
      have hl : τ.letterAt i = Letter.child := by
        simpa [L, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hm : i ∈ τ.childPositions := by simp [Context.childPositions, hiw, hl]
      have := (hmem i).mp hm
      omega
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hiw : b + n + i < τ.word.length := by
        simp only [R, List.length_drop] at hi
        omega
      have hl : τ.letterAt (b + n + i) = Letter.child := by
        simpa [R, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hm : b + n + i ∈ τ.childPositions := by
        simp [Context.childPositions, hiw, hl]
      have := (hmem _).mp hm
      omega
  have hEndpoint : ∀ (big small : Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      small.maxima.length < level →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      (p = 0 ∨ p = small.word.length) → big.bound = small.bound := by
    intro big small p level s ha hu hk hm hlevel hlen hp hbp hletter hedge
    have hf := fun fuel ↦ hFuel fuel big small p level s ha hu hk hm hlevel hlen hp hbp
      hletter hedge
    unfold bound
    rw [(hGeometry big small p level s hm hlevel hlen hp hbp hletter).1, List.length_map]
    exact hf _
  have hPoint : ∀ (big small : Context) p,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      (∀ N ∈ small.levels, big.extPositions N = (small.extPositions N).map (up p)) →
      (∀ N ∈ small.levels, big.sideAt N = small.sideAt N) → ∀ e,
      big.cupLimit (up p e) (up p e) = small.cupLimit e e ∧
      big.capLimit (up p e) (up p e) = small.capLimit e e := by
    intro big small p ha hu hk hm hext hsides
    have hlevels : ∀ s top, big.levelsOn s top = small.levelsOn s top := by
      intro t top
      unfold levelsOn levels
      rw [hm]
      apply List.filter_congr
      intro N hN
      rw [hsides N hN]
    have hExt : ∀ s top e,
        big.leftExt s top (up p e) = small.leftExt s top e ∧
        big.rightExt s top (up p e) = small.rightExt s top e := by
      intro t top e
      have hmap : ∀ ls ∈ (small.levelsOn t top).sublists,
          (ls.foldl (leftStep big) (up p e, 0)).2 =
            (ls.foldl (leftStep small) (e, 0)).2 ∧
          (ls.foldl (rightStep big) (up p e, 0)).2 =
            (ls.foldl (rightStep small) (e, 0)).2 := by
        intro ls hls
        apply hFolds big small p hext ls
        intro N hN
        exact (List.mem_filter.1 ((List.mem_sublists.1 hls).subset hN)).1
      constructor
      · rw [leftExt_eq, leftExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).1)
      · rw [rightExt_eq, rightExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).2)
    have hchain : ∀ s e,
        big.chainExt s (up p e) (up p e) = small.chainExt s e e := by
      intro t e
      unfold chainExt
      rw [(hExt t 0 e).1, (hExt t 0 e).2]
    have hjoin : ∀ s e,
        big.joinExt s (up p e) (up p e) = small.joinExt s e e := by
      intro t e
      unfold joinExt
      rw [hchain t e, hlevels]
      congr 3
      apply List.map_congr_left
      intro N hN
      rw [(hExt t N e).1, (hExt t N e).2]
      simp [maximumAt, hm]
    intro e
    constructor
    · unfold cupLimit
      rw [hu, hk, hchain, hjoin]
    · unfold capLimit
      rw [ha, hk, hchain, hjoin]
  have hDeletePoint : ∀ (big small : Context) p,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) → ∀ e,
      big.cupLimit (up p e) (up p e) = small.cupLimit e e ∧
      big.capLimit (up p e) (up p e) = small.capLimit e e := by
    intro big small p ha hu hk hm hlen hp hbp hletter
    have hext : ∀ N, big.extPositions N = (small.extPositions N).map (up p) := by
      intro N
      unfold extPositions
      rw [hlen]
      apply hFilter _ p _ _ hp
      · simp [hbp]
      · intro i hi
        rw [hletter i hi]
    have hsides : ∀ N, big.sideAt N = small.sideAt N := by
      intro N
      unfold sideAt
      rw [hext N, List.head?_map]
      cases hh : (small.extPositions N).head? with
      | none => rfl
      | some q =>
        simp only [Option.map_some]
        have hqn : q < small.word.length :=
          List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_head? hh)).1
        rw [hletter q hqn]
    exact hPoint big small p ha hu hk hm (fun N _ ↦ hext N) (fun N _ ↦ hsides N)
  have hStrip : ∀ (ρ : Context) (L T R : List Letter),
      ρ.word = L ++ T ++ R →
      (∀ x ∈ L ++ R, ∃ lev side, x = Letter.ext lev side ∧ ρ.maxima.length < lev) →
      ρ.bound = ({ ρ with word := T } : Context).bound := by
    intro ρ L
    induction L generalizing ρ with
    | nil =>
      intro T R hw hout
      simp only [List.nil_append] at hw hout
      induction R using List.reverseRecOn generalizing ρ with
      | nil =>
        exact congrArg Context.bound (hCtxEq _ _ rfl rfl rfl (by simpa using hw) rfl)
      | append_singleton R x ih =>
        obtain ⟨lev, side, rfl, hlev⟩ := hout x (by simp)
        let small : Context := { ρ with word := T ++ R }
        have hbig : ρ.word = (T ++ R) ++ [Letter.ext lev side] := by
          simpa only [List.append_assoc] using hw
        have hlen : ρ.word.length = small.word.length + 1 := by
          simp [hbig, small, Nat.add_assoc]
        have hp : ρ.letterAt small.word.length = Letter.ext lev side := by
          simp [letterAt, hbig, small]
        have hletter : ∀ i, i < small.word.length →
            ρ.letterAt (up small.word.length i) = small.letterAt i := by
          intro i hi
          simp only [up, if_pos hi, letterAt, hbig]
          rw [List.getElem?_append_left (show i < (T ++ R).length from hi)]
        have hstep := hEndpoint ρ small small.word.length lev side rfl rfl rfl rfl
          hlev hlen le_rfl hp hletter (Or.inr rfl)
        exact hstep.trans (ih small rfl (fun y hy ↦ hout y (by simp [hy])))
    | cons x L ih =>
      intro T R hw hout
      obtain ⟨lev, side, rfl, hlev⟩ := hout x (by simp)
      let small : Context := { ρ with word := L ++ T ++ R }
      have hbig : ρ.word = Letter.ext lev side :: (L ++ T ++ R) := by simpa using hw
      have hlen : ρ.word.length = small.word.length + 1 := by simp [hbig, small]
      have hp : ρ.letterAt 0 = Letter.ext lev side := by simp [letterAt, hbig]
      have hletter : ∀ i, i < small.word.length →
          ρ.letterAt (up 0 i) = small.letterAt i := by
        intro i hi
        simp [up, letterAt, hbig, small]
      have hstep := hEndpoint ρ small 0 lev side rfl rfl rfl rfl hlev hlen
        (Nat.zero_le _) hp hletter (Or.inl rfl)
      exact hstep.trans (ih small T R rfl (fun y hy ↦ hout y (by simp [hy])))
  have hPartWord : ∀ (τ : Context) (L R : List Letter) N keep s m,
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate N Letter.child ++ R →
      (τ.part keep s m).word = L.map shift ++
        ((List.range N).map fun i ↦ if i + L.length ∈ keep then Letter.child
          else Letter.ext 1 s) ++ R.map shift := by
    intro τ L R N keep s m hout hw
    rw [hPartMap, hw]
    simp only [List.mapIdx_append, List.length_append, List.length_replicate]
    have hL := hMapExt L keep s 0 (fun x hx ↦ hout x (List.mem_append_left _ hx))
    simp only [Nat.add_zero] at hL
    rw [hL, hMapExt R keep s _ (fun x hx ↦ hout x (List.mem_append_right _ hx))]
    have hmid : (List.replicate N Letter.child).mapIdx
        (fun i x ↦ replace keep s (i + L.length) x) =
        (List.range N).map (fun i ↦ if i + L.length ∈ keep then Letter.child
          else Letter.ext 1 s) := by
      apply List.ext_getElem (by simp)
      intro i hi hj
      simp [replace]
    rw [hmid]
  have hEraseLetter (ρ : Context) (p i : ℕ) :
      ({ ρ with word := ρ.word.eraseIdx p } : Context).letterAt i =
        ρ.letterAt (up p i) := by
    simp only [letterAt, List.getElem?_eraseIdx, up]
    split <;> rfl
  have hPartErase : ∀ (ρ : Context) p keep s m, p < ρ.word.length →
      let small : Context := { ρ with word := ρ.word.eraseIdx p }
      let kept := (List.range small.word.length).filter (fun i ↦ up p i ∈ keep)
      (small.part kept s m).word = (ρ.part keep s m).word.eraseIdx p := by
    intro ρ p keep s m hp
    dsimp only
    let small : Context := { ρ with word := ρ.word.eraseIdx p }
    let kept := (List.range small.word.length).filter (fun i ↦ up p i ∈ keep)
    let π := ρ.part keep s m
    change (small.part kept s m).word = π.word.eraseIdx p
    apply List.ext_getElem
    · rw [part_word_length]
      change (ρ.word.eraseIdx p).length = ((ρ.part keep s m).word.eraseIdx p).length
      rw [List.length_eraseIdx_of_lt hp, List.length_eraseIdx_of_lt
        (by simpa only [part_word_length] using hp), part_word_length]
    · intro i hi hj
      have hi' : i < small.word.length := by simpa only [part_word_length] using hi
      have hlen : small.word.length = ρ.word.length - 1 := List.length_eraseIdx_of_lt hp
      have hup' : up p i < ρ.word.length := by
        dsimp [up]
        split_ifs <;> omega
      have hk : i ∈ kept ↔ up p i ∈ keep := by simp [kept, hi']
      have hletter : (small.part kept s m).letterAt i =
          ({ π with word := π.word.eraseIdx p } : Context).letterAt i := by
        rw [hEraseLetter]
        cases he : ρ.letterAt (up p i) with
        | child =>
          rw [part_letterAt_of_child small kept s m hi'
            ((hEraseLetter ρ p i).trans he), part_letterAt_of_child ρ keep s m hup' he]
          simp only [hk]
        | ext lev side =>
          rw [part_letterAt_of_ext small kept s m hi'
            ((hEraseLetter ρ p i).trans he), part_letterAt_of_ext ρ keep s m hup' he]
      simpa only [letterAt, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hj, Option.getD_some] using hletter
  have hNormalizePart : ∀ (ρ : Context) b N,
      ρ.childPositions = List.range' b N →
      (∀ p lev side, ρ.letterAt p = Letter.ext lev side → 1 ≤ lev) →
      ∀ keep s m,
      (ρ.part keep s m).bound =
        ({ a := ρ.capLimit b b + 1, u := ρ.cupLimit b b + 1, k := ρ.k,
           word := (ρ.part keep s m).word, maxima := [m] } : Context).bound := by
    intro ρ b N hpos hpositive keep s m
    let π := ρ.part keep s m
    have hhist : π.a = ρ.a ∧ π.u = ρ.u ∧ π.k = ρ.k ∧
        π.maxima.length = 1 + ρ.maxima.length ∧
        (∀ l, 1 ≤ l → π.extPositions (l + 1) = ρ.extPositions l) ∧
        (∀ l, 1 ≤ l → π.sideAt (l + 1) = ρ.sideAt l) ∧
        (∀ l, 1 ≤ l → π.maximumAt (l + 1) = ρ.maximumAt l) := by
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [π, part_maxima, Nat.add_comm]
      · exact fun l hl ↦ part_extPositions_succ ρ keep s m hl
      · exact fun l hl ↦ part_sideAt_succ ρ keep s m hl
      · exact fun l hl ↦ part_maximumAt_succ ρ keep s m hl
    have hnew : ∀ l x, 1 ≤ l → l ≤ 1 → x ∈ π.extPositions l →
        x ∈ ρ.childPositions := by
      intro l x hl hl1 hx
      have : l = 1 := by omega
      subst l
      rw [part_extPositions_one hpositive keep s m] at hx
      exact (List.mem_filter.1 hx).1
    have hchild : ∀ x ∈ π.childPositions, x ∈ ρ.childPositions := by
      intro x hx
      rw [part_childPositions] at hx
      exact (List.mem_filter.1 hx).1
    have hposπ : ∀ x lev side, π.letterAt x = Letter.ext lev side → 1 ≤ lev := by
      intro x lev side hx
      have hxl : x < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le π
          (show π.word.length ≤ x by rw [part_word_length]; omega)
        rw [hn] at hx
        cases hx
      cases he : ρ.letterAt x with
      | child =>
        rw [part_letterAt_of_child ρ keep s m hxl he] at hx
        split at hx
        · cases hx
        · cases hx
          omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext ρ keep s m hxl he] at hx
        cases hx
        omega
    exact (ctx_single_run_descendant_bound_normalize ρ b N hpos π 1 hhist hnew hchild
      hposπ).2
  have hEraseMiddle (L T R : List Letter) (p : ℕ)
      (hpL : L.length ≤ p) (hpT : p - L.length < T.length) :
      (L ++ T ++ R).eraseIdx p = L ++ T.eraseIdx (p - L.length) ++ R := by
    rw [List.append_assoc, List.eraseIdx_append_of_length_le hpL,
      List.eraseIdx_append_of_lt_length hpT]
    exact List.append_assoc .. |>.symm
  let π := σ.part keep s m
  let p := left.length
  have hπp : π.letterAt p = Letter.child := by
    simp [π, p, letterAt, hword]
  have hπp1 : π.letterAt (p + 1) = Letter.child := by
    simp [π, p, letterAt, hword]
  have hp1 : p + 1 < σ.word.length := by
    have hlen : σ.word.length = left.length + 2 + right.length := by
      rw [← part_word_length σ keep s m, hword]
      simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp [p]
    omega
  have hpmem : p ∈ σ.childPositions := by
    have hh : p ∈ π.childPositions := by
      simp only [childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by simpa only [π, part_word_length] using (show p < σ.word.length by omega),
        hπp⟩
    rw [part_childPositions] at hh
    exact (List.mem_filter.1 hh).1
  have hp1mem : p + 1 ∈ σ.childPositions := by
    have hh : p + 1 ∈ π.childPositions := by
      simp only [childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by simpa only [π, part_word_length] using hp1, hπp1⟩
    rw [part_childPositions] at hh
    exact (List.mem_filter.1 hh).1
  have hne : σ.childPositions ≠ [] := by intro hn; simp [hn] at hpmem
  obtain ⟨b, hpos⟩ := hInterval σ hruns hne
  let N := σ.childPositions.length
  change σ.childPositions = List.range' b N at hpos
  have hpb : b ≤ p ∧ p < b + N := by simpa only [hpos, List.mem_range'_1] using hpmem
  have hp1b : b ≤ p + 1 ∧ p + 1 < b + N := by
    simpa only [hpos, List.mem_range'_1] using hp1mem
  have hN : 2 ≤ N := by omega
  obtain ⟨L, R, hLb, hσword, hout⟩ := hReconstruct σ b N (by omega) hpos
  let small : Context := { σ with word := σ.word.eraseIdx p }
  let kept := (List.range small.word.length).filter (fun i ↦ up p i ∈ keep)
  let π' := small.part kept s m
  have hsmallword : small.word = L ++ List.replicate (N - 1) Letter.child ++ R := by
    change σ.word.eraseIdx p = _
    rw [hσword, hEraseMiddle L (List.replicate N Letter.child) R p
      (by omega) (by simp; omega), List.eraseIdx_replicate, if_pos (by omega)]
  have hsmallpos : small.childPositions = List.range' b (N - 1) := by
    rw [← hLb]
    exact hPositions small L R (N - 1) hout hsmallword
  have hpositive : ∀ q lev side, σ.letterAt q = Letter.ext lev side → 1 ≤ lev :=
    fun q lev side h ↦ (hwf.2.2.2.2.2 q lev side h).1
  have hsmallpositive : ∀ q lev side,
      small.letterAt q = Letter.ext lev side → 1 ≤ lev := by
    intro q lev side h
    exact hpositive (up p q) lev side ((hEraseLetter σ p q).symm.trans h)
  have hσp : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.1 hpmem).2
  have hlen : σ.word.length = small.word.length + 1 := by
    have he := List.length_eraseIdx_of_lt (show p < σ.word.length by omega)
    change σ.word.length = (σ.word.eraseIdx p).length + 1
    omega
  have hpc : p ≤ small.word.length := by omega
  have hletter : ∀ i, i < small.word.length → σ.letterAt (up p i) = small.letterAt i :=
    fun i _ ↦ (hEraseLetter σ p i).symm
  have hb : b ∈ σ.childPositions := by rw [hpos, List.mem_range'_1]; omega
  have hbb : up p b ∈ σ.childPositions := by
    rw [hpos, List.mem_range'_1]
    dsimp [up]
    split_ifs <;> omega
  have hconstant := ctx_point_limits_eq_of_child_interval σ b (up p b) hb hbb
    (by dsimp [up]; split_ifs <;> omega) (by
      intro r hbr hrb
      rw [hpos, List.mem_range'_1]
      dsimp [up] at hrb
      split_ifs at hrb <;> omega)
  have hdeleted := hDeletePoint σ small p rfl rfl rfl rfl hlen hpc hσp hletter b
  have hcup : σ.cupLimit b b = small.cupLimit b b := hconstant.1.trans hdeleted.1
  have hcap : σ.capLimit b b = small.capLimit b b := hconstant.2.trans hdeleted.2
  let T := (List.range N).map (fun i ↦ if i + L.length ∈ keep then Letter.child
    else Letter.ext 1 s)
  have hTlen : T.length = N := by simp [T]
  have hπword : π.word = L.map shift ++ T ++ R.map shift :=
    hPartWord σ L R N keep s m hout hσword
  have hπ'word : π'.word = L.map shift ++ T.eraseIdx (p - b) ++ R.map shift := by
    rw [hPartErase σ p keep s m (by omega), hπword]
    rw [hEraseMiddle (L.map shift) T (R.map shift) p (by simp; omega)
      (by simp; omega)]
    simp only [List.length_map, hLb]
  have hπ'contract : π'.word = left ++ [Letter.child] ++ right := by
    rw [hPartErase σ p keep s m (by omega), hword]
    simp only [List.append_assoc]
    rw [List.eraseIdx_append_of_length_le (show left.length ≤ p from le_rfl)]
    simp [p]
  have hNorm := hNormalizePart σ b N hpos hpositive keep s m
  have hNorm' := hNormalizePart small b (N - 1) hsmallpos hsmallpositive kept s m
  let τ : Context :=
    { a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1,
      k := σ.k, word := π.word, maxima := [m] }
  let τ' : Context := { τ with word := π'.word }
  have hnorm : π.bound = τ.bound := hNorm
  have hnorm' : π'.bound = τ'.bound := by
    simpa only [← hcup, ← hcap] using hNorm'
  have hinert : ∀ x ∈ L.map shift ++ R.map shift,
      ∃ lev side, x = Letter.ext lev side ∧ τ.maxima.length < lev := by
    intro x hx
    rw [← List.map_append] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyword : y ∈ σ.word := by
      rw [hσword]
      rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ (List.mem_append_left _ hy)
      · exact List.mem_append_right _ hy
    cases he : y with
    | child => exact (hout _ hy he).elim
    | ext lev side =>
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hyword
      have hlev := hpositive q lev side (by simpa only [letterAt, hq] using he)
      exact ⟨lev + 1, side, rfl, by simp [τ]; omega⟩
  have hstrip := hStrip τ (L.map shift) T (R.map shift) hπword hinert
  have hstrip' := hStrip τ' (L.map shift) (T.eraseIdx (p - b)) (R.map shift) hπ'word
    hinert
  let active : Letter → Bool
    | .child => true
    | .ext lev _ => decide (lev = 1)
  have hTletters : ∀ x ∈ T, x = Letter.child ∨ x = Letter.ext 1 s := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    split <;> simp
  have hTfilter : T.filter active = T := by
    apply List.filter_eq_self.2
    intro x hx
    rcases hTletters x hx with rfl | rfl <;> rfl
  have houterfilter : (L.map shift).filter active = [] ∧
      (R.map shift).filter active = [] := by
    constructor <;> apply List.filter_eq_nil_iff.2 <;> intro x hx
    · obtain ⟨lev, side, rfl, hlev⟩ := hinert x (List.mem_append_left _ hx)
      have hn : lev ≠ 1 := by simp only [τ, List.length_singleton] at hlev; omega
      simp [active, hn]
    · obtain ⟨lev, side, rfl, hlev⟩ := hinert x (List.mem_append_right _ hx)
      have hn : lev ≠ 1 := by simp only [τ, List.length_singleton] at hlev; omega
      simp [active, hn]
  have hT'filter : (T.eraseIdx (p - b)).filter active = T.eraseIdx (p - b) := by
    apply List.filter_eq_self.2
    intro x hx
    rcases hTletters x (List.mem_of_mem_eraseIdx hx) with rfl | rfl <;> rfl
  have hfiltered : left.filter active ++ [Letter.child, Letter.child] ++
      right.filter active = T := by
    have hh := congrArg (List.filter active) hword
    rw [hπword, List.filter_append, List.filter_append, houterfilter.1,
      houterfilter.2, hTfilter] at hh
    simpa [List.filter_append, active] using hh.symm
  have hfiltered' : left.filter active ++ [Letter.child] ++ right.filter active =
      T.eraseIdx (p - b) := by
    have hh := congrArg (List.filter active) hπ'contract
    rw [hπ'word, List.filter_append, List.filter_append, houterfilter.1,
      houterfilter.2, hT'filter] at hh
    simpa [List.filter_append, active] using hh.symm
  have hallowed : ∀ x ∈ left.filter active ++ right.filter active,
      x = Letter.child ∨ x = Letter.ext 1 s := by
    intro x hx
    apply hTletters x
    rw [← hfiltered]
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_right _ hx
  have hk : 3 ≤ σ.k := by omega
  have ha : σ.capLimit b b + 1 ≤ σ.k := by
    have hh : σ.capLimit b b ≤ σ.k - 1 :=
      (Nat.min_le_right _ _).trans (Nat.sub_le ..)
    omega
  have hu : σ.cupLimit b b + 1 ≤ σ.k := by
    have hh : σ.cupLimit b b ≤ σ.k - 1 :=
      (Nat.min_le_right _ _).trans (Nat.sub_le ..)
    omega
  have hc := hroot (σ.capLimit b b + 1) (σ.cupLimit b b + 1) σ.k m hk
    (by omega) ha (by omega) hu hm hmk s (left.filter active) (right.filter active)
    hallowed
  rw [hfiltered, hfiltered'] at hc
  have heq : ({ π with word := left ++ [Letter.child] ++ right } : Context) = π' :=
    hCtxEq _ _ rfl rfl rfl hπ'contract.symm rfl
  calc
    π.bound = τ.bound := hnorm
    _ = ({ τ with word := T } : Context).bound := hstrip
    _ = ({ τ' with word := T.eraseIdx (p - b) } : Context).bound := hc
    _ = τ'.bound := hstrip'.symm
    _ = π'.bound := hnorm'.symm
    _ = ({ π with word := left ++ [Letter.child] ++ right } : Context).bound :=
      congrArg Context.bound heq.symm
end ErdosSzekeres
