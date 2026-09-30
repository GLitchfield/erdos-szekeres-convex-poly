import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ESBlueprint.B.CtxBoundAdditivePrefixSuffix
import ESBlueprint.B.CtxBoundCutLe

set_option maxHeartbeats 8000000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- External-letter deletion monotonicity for contexts whose child letters are pairwise non-adjacent (every run a single child): deleting an external letter whose level keeps another letter cannot decrease the bound. The level-keeps-a-letter hypothesis is necessary (deleting the last letter of an upper level flips sideAt to lower and can add a join term). Proof route: replace the letter by an inert letter (ctx_bound_mono_of_marker_inclusion: limits and every fuel approximation only grow), then delete the inert letter by induction on fuel (limits unchanged, blocks and parts correspond); a merge to a single run can only produce two adjacent children, whose only cuts are prefix/suffix (ctx_bound_additive_prefix_suffix). Used with run contraction (C1) to shorten alternating partitions of a single run by two children (R7, runs/claude-comb-closedform-20260930). Evidence (compiled evaluator, diagnostic): 0 violations in 82,512 deletions over eight triples, 2-4 children (runs/claude-comb-closedform-20260930/d1/).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_mono_of_marker_inclusion, ErdosSzekeres.ctx_bound_additive_prefix_suffix, ErdosSzekeres.decomposableThreshold_mono
@consumer ErdosSzekeres.ctx_bound_additive_single_run_alternating -/
theorem ctx_bound_ext_letter_deletion_mono_of_isolated_children (σ : Ctx.Context) (hwf : σ.WellFormed) (hiso : ∀ p ∈ σ.childPositions, p + 1 ∉ σ.childPositions) (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side) (hword : σ.word = left ++ [Ctx.Letter.ext lev side] ++ right) (hother : Ctx.Letter.ext lev side ∈ left ++ right) : σ.bound ≤ ({ σ with word := left ++ right } : Ctx.Context).bound := by
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
  have hIsolatedRuns (big : Context)
      (hiso : ∀ i ∈ big.childPositions, i + 1 ∉ big.childPositions) :
      big.numRuns = big.childPositions.length := by
    unfold numRuns childPositions
    congr 1
    apply List.filter_congr
    intro i hi
    simp only [decide_eq_decide]
    constructor
    · exact And.left
    · intro hchild
      refine ⟨hchild, ?_⟩
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      · right
        intro hprev
        have himem : i ∈ big.childPositions := by
          simp only [childPositions, List.mem_filter, decide_eq_true_eq]
          exact ⟨hi, hchild⟩
        have hprevmem : i - 1 ∈ big.childPositions := by
          simp only [childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨by have := List.mem_range.1 hi; omega, hprev⟩
        have := hiso (i - 1) hprevmem
        have heq : i - 1 + 1 = i := by omega
        exact this (heq.symm ▸ himem)
  have hAdjacent (big small : Context) (p : ℕ)
      (hc : big.childPositions = small.childPositions.map (up p))
      (hiso : ∀ i ∈ big.childPositions, i + 1 ∉ big.childPositions) :
      ∀ i ∈ small.childPositions, i + 1 ∈ small.childPositions → i + 1 = p := by
    intro i hi hnext
    by_contra hne
    have hib : up p i ∈ big.childPositions := by rw [hc]; exact List.mem_map_of_mem hi
    have hnb : up p (i + 1) ∈ big.childPositions := by
      rw [hc]; exact List.mem_map_of_mem hnext
    have heq : up p (i + 1) = up p i + 1 := by
      dsimp [up]
      split_ifs <;> omega
    exact hiso _ hib (heq ▸ hnb)
  have hInterval (ρ : Context) (hruns : ρ.numRuns ≤ 1) (hchildNe : ρ.childPositions ≠ []) :
      ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ ρ.childPositions := by
      rw [hcons]
      exact List.mem_cons_self
    have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
      (childPositions_pairwise ρ).imp le_of_lt
    have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range ρ.word.length).filter fun p ↦
      ρ.letterAt p = Letter.child ∧ (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child)
    have hstartsLen : starts.length ≤ 1 := by
      simpa [starts, numRuns] using hruns
    have hstartsNodup : starts.Nodup := List.nodup_range.filter _
    have hbRange : b < ρ.word.length := List.mem_range.1 (List.mem_filter.1 hb).1
    have hbLetter : ρ.letterAt b = Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition : b = 0 ∨ ρ.letterAt (b - 1) ≠ Letter.child := by
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
      have htwo : ({b, p} : Finset ℕ).card = 2 := by simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
      intro p hp hpb
      have hpRange : p < ρ.word.length := List.mem_range.1 (List.mem_filter.1 hp).1
      have hpLetter : ρ.letterAt p = Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by have := hmin p hp; omega
      by_contra hprevMem
      have hprevLetter : ρ.letterAt (p - 1) ≠ Letter.child := by
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
    have he : e ∈ ρ.childPositions := by dsimp [e]; exact List.getLast_mem _
    have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
      intro p hp
      simpa [e] using hordered.rel_getLast hp
    have hbe : b ≤ e := hmin e he
    have hmemRange : ∀ p, p ∈ ρ.childPositions ↔ p ∈ List.range' b (e + 1 - b) := by
      intro p
      simp only [List.mem_range'_1]
      constructor
      · intro hp
        exact ⟨hmin p hp, by have := hmax p hp; omega⟩
      · rintro ⟨hbp, hp⟩
        exact hfill e he p hbp (by omega)
    have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
      (List.perm_ext_iff_of_nodup (childPositions_nodup ρ) List.nodup_range').2 hmemRange
    have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
      List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
    have hlen : ρ.childPositions.length = e + 1 - b := by rw [hrange]; simp
    exact ⟨b, by rw [hlen]; exact hrange⟩
  have hMerge (big small : Context) p
      (hc : big.childPositions = small.childPositions.map (up p))
      (hiso : ∀ i ∈ big.childPositions, i + 1 ∉ big.childPositions)
      (hbig : 2 ≤ big.numRuns) (hsmall : small.numRuns ≤ 1) :
      ∃ b, small.childPositions = List.range' b 2 := by
    have hlen : 2 ≤ small.childPositions.length := by
      have hle := numRuns_le_length big
      rw [hc, List.length_map] at hle
      omega
    have hne : small.childPositions ≠ [] := by intro hnil; simp [hnil] at hlen
    obtain ⟨b, hinterval⟩ := hInterval small hsmall hne
    have htwo : small.childPositions.length = 2 := by
      by_contra hn
      have hb : b ∈ small.childPositions := by
        rw [hinterval]; simp only [List.mem_range'_1]; omega
      have hb1 : b + 1 ∈ small.childPositions := by
        rw [hinterval]; simp only [List.mem_range'_1]; omega
      have hb2 : (b + 1) + 1 ∈ small.childPositions := by
        rw [hinterval]; simp only [List.mem_range'_1]; omega
      have h1 := hAdjacent big small p hc hiso b hb hb1
      have h2 := hAdjacent big small p hc hiso (b + 1) hb1 hb2
      omega
    exact ⟨b, by simpa only [htwo] using hinterval⟩
  have hMergeCuts (small : Context) (hwf : small.WellFormed) (b : ℕ)
      (hps : small.childPositions = List.range' b 2) (B : List ℕ) (hB : B ∈ small.blocks)
      (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ small.k - 2) :
      (small.part B Side.lower d).bound +
          (small.part (small.childPositions.filter (· ∉ B)) Side.upper
            (small.k - 1 - d)).bound ≤ small.bound ∧
      (small.part B Side.upper (small.k - 1 - d)).bound +
          (small.part (small.childPositions.filter (· ∉ B)) Side.lower d).bound ≤
        small.bound := by
    have hblocks : small.blocks = [[b], [b + 1]] := by
      simp [blocks, hps, List.range'_succ, List.range_succ]
    have hcut := ctx_bound_additive_prefix_suffix small hwf b 1 1 hps
      (by omega) (by omega) d hd hdk
    have hprefix : List.range' b 1 = [b] := by simp [List.range'_succ]
    have hsuffix : List.range' (b + 1) 1 = [b + 1] := by simp [List.range'_succ]
    rw [hprefix, hsuffix] at hcut
    rw [hblocks] at hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · have hrest : small.childPositions.filter (· ∉ [b]) = [b + 1] := by
        simp [hps, List.range'_succ]
      simpa only [hrest] using hcut
    · have hrest : small.childPositions.filter (· ∉ [b + 1]) = [b] := by
        simp [hps, List.range'_succ]
      constructor
      · simpa only [hrest, Nat.add_comm] using hcut.2
      · simpa only [hrest, Nat.add_comm] using hcut.1
  have hFuel : ∀ fuel (big small : Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      small.maxima.length < level →
      big.word.length = small.word.length + 1 → p ≤ small.word.length →
      big.letterAt p = Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      (∀ i ∈ big.childPositions, i + 1 ∉ big.childPositions) → small.WellFormed →
      boundFuel fuel big ≤ small.bound := by
    intro fuel
    induction fuel with
    | zero => intros; exact Nat.zero_le _
    | succ fuel ih =>
      intro big small p level s ha hu hk hm hlevel hlen hp hbp hletter hiso hwf
      obtain ⟨hc, hext, hsides⟩ :=
        hGeometry big small p level s hm hlevel hlen hp hbp hletter
      have hparts : ∀ (B : List ℕ) (t : Side) m, 1 ≤ m → m ≤ small.k - 2 →
          boundFuel fuel (big.part (B.map (up p)) t m) ≤ (small.part B t m).bound := by
        intro B t m hm1 hmk
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
        · intro i hi hnext
          rw [part_childPositions] at hi hnext
          exact hiso i (List.mem_filter.1 hi).1 (List.mem_filter.1 hnext).1
        · exact hwf.part B t hm1 hmk
      rw [boundFuel.eq_2 big fuel]
      by_cases hrun : big.numRuns ≤ 1
      · rw [if_pos hrun, hBase big small p level s ha hu hk hm hlevel hlen hp hbp hletter]
        have hsmallrun : small.numRuns ≤ 1 := by
          rw [hIsolatedRuns big hiso, hc, List.length_map] at hrun
          exact (numRuns_le_length small).trans hrun
        have hbound : small.bound = small.base := by
          simp only [bound, boundFuel.eq_2, if_pos hsmallrun]
        exact hbound.ge
      · rw [if_neg hrun]
        dsimp only
        rw [hc, hBlocks big small p hc, hk, List.flatMap_map]
        apply getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        obtain ⟨B, hB, d', hd', hx⟩ := hx
        rw [hRest] at hx
        have hd : 1 ≤ d' + 1 := by omega
        have hdk : d' + 1 ≤ small.k - 2 := by omega
        have hc1 : 1 ≤ small.k - 1 - (d' + 1) := by omega
        have hck : small.k - 1 - (d' + 1) ≤ small.k - 2 := by omega
        have hcut :
            (small.part B Side.lower (d' + 1)).bound +
                (small.part (small.childPositions.filter (· ∉ B)) Side.upper
                  (small.k - 1 - (d' + 1))).bound ≤ small.bound ∧
            (small.part B Side.upper (small.k - 1 - (d' + 1))).bound +
                (small.part (small.childPositions.filter (· ∉ B)) Side.lower
                  (d' + 1)).bound ≤ small.bound := by
          by_cases hsrun : small.numRuns ≤ 1
          · obtain ⟨b, hps⟩ := hMerge big small p hc hiso (by omega) hsrun
            exact hMergeCuts small hwf b hps B hB (d' + 1) hd hdk
          · exact ctx_bound_cut_le small (by omega) B hB (d' + 1) hd hdk
        rcases hx with rfl | rfl
        · exact (Nat.add_le_add (hparts B Side.lower (d' + 1) hd hdk)
            (hparts (small.childPositions.filter (· ∉ B)) Side.upper
              (small.k - 1 - (d' + 1)) hc1 hck)).trans hcut.1
        · exact (Nat.add_le_add (hparts B Side.upper
              (small.k - 1 - (d' + 1)) hc1 hck)
            (hparts (small.childPositions.filter (· ∉ B)) Side.lower
              (d' + 1) hd hdk)).trans hcut.2
  have hSideOfLetter (ρ : Context) (N : ℕ) (v : Side) (q : ℕ)
      (hq : ρ.letterAt q = Letter.ext N v)
      (huniform : ∀ p w, ρ.letterAt p = Letter.ext N w → w = v) : ρ.sideAt N = v := by
    have hqn : q < ρ.word.length := by
      by_contra hge
      rw [letterAt_of_length_le _ (by omega)] at hq
      cases hq
    have hqmem : q ∈ ρ.extPositions N := by
      simp only [extPositions, List.mem_filter, List.mem_range]
      exact ⟨hqn, by simp [hq]⟩
    unfold sideAt
    cases hh : (ρ.extPositions N).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.1 hh
      rw [hnil] at hqmem
      simp at hqmem
    | some p =>
      have hp := List.mem_filter.1 (List.mem_of_mem_head? hh)
      cases he : ρ.letterAt p with
      | child => simp [he] at hp
      | ext j w =>
        have hj : j = N := by simpa [he] using hp.2
        subst j
        simp only [he]
        exact huniform p w he
  let small : Context := { σ with word := left ++ right }
  let p := left.length
  have hsw : small.word = left ++ right := rfl
  have hbw : σ.word = left ++ Letter.ext lev side :: right := by
    simpa only [List.append_assoc, List.singleton_append] using hword
  have hp : p ≤ small.word.length := by simp [p, hsw]
  have hpbig : p < σ.word.length := by simp [p, hbw]
  have hlen : σ.word.length = small.word.length + 1 := by simp [hsw, hbw]; omega
  have hbp : σ.letterAt p = Letter.ext lev side := by
    unfold letterAt
    rw [hbw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hletter : ∀ i, i < small.word.length → σ.letterAt (up p i) = small.letterAt i := by
    intro i hi
    by_cases hip : i < p
    · have hil : i < left.length := hip
      simp only [up, if_pos hip, letterAt, hsw, hbw, List.getElem?_append_left hil]
    · have hpi : left.length ≤ i := Nat.le_of_not_gt hip
      have hpi' : left.length ≤ i + 1 := by omega
      have hsub : i + 1 - left.length = (i - left.length) + 1 := by omega
      simp only [up, if_neg hip, letterAt, hsw, hbw,
        List.getElem?_append_right hpi', List.getElem?_append_right hpi,
        hsub, List.getElem?_cons_succ]
  have hsmallLen {q N v} (hq : small.letterAt q = Letter.ext N v) :
      q < small.word.length := by
    by_contra hge
    rw [letterAt_of_length_le _ (by omega)] at hq
    cases hq
  have hsmallWf : small.WellFormed := by
    obtain ⟨ha, hu, hak, huk, hmax, htags⟩ := hwf
    refine ⟨ha, hu, hak, huk, hmax, ?_⟩
    intro q N v hq
    obtain ⟨hN1, hNdepth, hNv⟩ := htags (up p q) N v
      ((hletter q (hsmallLen hq)).trans hq)
    refine ⟨hN1, hNdepth, ?_⟩
    apply Eq.symm
    apply hSideOfLetter small N v q hq
    intro r w hr
    have hrw := (htags (up p r) N w ((hletter r (hsmallLen hr)).trans hr)).2.2
    exact hrw.trans hNv.symm
  have hpositive : ∀ q N v, σ.letterAt q = Letter.ext N v → 1 ≤ N :=
    fun q N v hq ↦ (hwf.2.2.2.2.2 q N v hq).1
  have hlev := hwf.2.2.2.2.2 p lev side hbp
  have hN : lev ∈ σ.levels := by
    refine List.mem_map.2 ⟨lev - 1, List.mem_range.2 (by omega), ?_⟩
    omega
  obtain ⟨w, hw⟩ := List.mem_iff_getElem?.1 hother
  have hwn : w < small.word.length := by
    have := List.getElem?_eq_some_iff.1 hw
    exact this.1
  have hwletter : small.letterAt w = Letter.ext lev side := by
    simp only [letterAt, hsw, hw, Option.getD_some]
  have hupn : up p w < σ.word.length := by
    rw [hlen]
    dsimp [up]
    split_ifs <;> omega
  have hupp : up p w ≠ p := by
    dsimp [up]
    split_ifs <;> omega
  let keep := (List.range σ.word.length).filter (· ≠ p)
  have hwext : up p w ∈ σ.extPositions lev := by
    simp only [extPositions, List.mem_filter, List.mem_range]
    exact ⟨hupn, by rw [hletter w hwn, hwletter]; simp⟩
  have hwkeep : up p w ∈ keep := by simp [keep, hupn, hupp]
  let inert : Context := { σ with word := (List.range σ.word.length).map (fun q ↦
    match σ.letterAt q with
    | Letter.child => Letter.child
    | Letter.ext j v => if j = lev then
        if q ∈ keep then Letter.ext lev (σ.sideAt lev)
        else Letter.ext (σ.maxima.length + 1) v
        else Letter.ext j v) }
  have hprune := ctx_single_level_occurrence_prune_bound_mono σ hpositive lev hN
    keep (up p w) hwext hwkeep
  change (∀ q N v, inert.letterAt q = Letter.ext N v → 1 ≤ N) ∧
    inert.childPositions = σ.childPositions ∧
    (∀ j ∈ σ.levels, inert.sideAt j = σ.sideAt j ∧ inert.maximumAt j = σ.maximumAt j ∧
      inert.extPositions j = if j = lev then (σ.extPositions j).filter (· ∈ keep)
        else σ.extPositions j) ∧
    (∀ t : Side, σ.sideAt lev ≠ t → ∀ top q,
      inert.leftExt t top q = σ.leftExt t top q ∧
        inert.rightExt t top q = σ.rightExt t top q) ∧
    (∀ q r, σ.cupLimit q r ≤ inert.cupLimit q r ∧ σ.capLimit q r ≤ inert.capLimit q r) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel inert) ∧ σ.bound ≤ inert.bound at hprune
  have hInertLetter (q : ℕ) (hq : q < σ.word.length) :
      inert.letterAt q = (match σ.letterAt q with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = lev then
            if q ∈ keep then Letter.ext lev (σ.sideAt lev)
            else Letter.ext (σ.maxima.length + 1) v
            else Letter.ext j v) := by
    simp only [inert, letterAt, List.getElem?_map, List.getElem?_range hq,
      Option.map_some, Option.getD_some]
  have hip : inert.letterAt p = Letter.ext (σ.maxima.length + 1) side := by
    rw [hInertLetter p hpbig, hbp]
    simp [keep]
  have hiletter : ∀ i, i < small.word.length →
      inert.letterAt (up p i) = small.letterAt i := by
    intro i hi
    have hin : up p i < σ.word.length := by
      rw [hlen]
      dsimp [up]
      split_ifs <;> omega
    have hne : up p i ≠ p := by dsimp [up]; split_ifs <;> omega
    have hkeep : up p i ∈ keep := by simp [keep, hin, hne]
    rw [hInertLetter _ hin]
    cases he : σ.letterAt (up p i) with
    | child => simpa only [he] using hletter i hi
    | ext j v =>
      by_cases hj : j = lev
      · subst j
        have hv := (hwf.2.2.2.2.2 (up p i) lev v he).2.2
        simpa [he, hkeep, hv] using hletter i hi
      · simpa only [he, if_neg hj] using hletter i hi
  have hiiso : ∀ q ∈ inert.childPositions, q + 1 ∉ inert.childPositions := by
    simpa only [hprune.2.1] using hiso
  have hibound : inert.bound ≤ small.bound := by
    apply hFuel _ inert small p (σ.maxima.length + 1) side rfl rfl rfl rfl
    · exact Nat.lt_succ_self _
    · simpa only [inert, List.length_map, List.length_range] using hlen
    · exact hp
    · exact hip
    · exact hiletter
    · exact hiiso
    · exact hsmallWf
  exact hprune.2.2.2.2.2.2.trans hibound

end ErdosSzekeres
