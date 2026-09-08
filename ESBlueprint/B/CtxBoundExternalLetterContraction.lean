import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

set_option maxHeartbeats 8000000

/-- Deleting one of two adjacent identical external letters preserves the context bound, with parameters and sibling maxima fixed. The proof must transport child positions, ordered extension folds, and recursive cuts; this makes no assertion about contracting child letters.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_approved_external.py -/
theorem ctx_bound_external_letter_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side)
  (hword : σ.word = left ++ [Ctx.Letter.ext lev side, Ctx.Letter.ext lev side] ++ right) :
  σ.bound = ({ σ with word := left ++ [Ctx.Letter.ext lev side] ++ right } : Ctx.Context).bound := by
  classical
  let up (p i : ℕ) := if i < p then i else i + 1
  let down (p i : ℕ) := if i ≤ p then i else i + 1
  let expand (p i : ℕ) := if i = p then [i, i + 1] else [up p i]
  have hup : ∀ p, StrictMono (up p) := by
    intro p i j hij
    dsimp [up]
    split_ifs <;> omega
  have hdown : ∀ p, StrictMono (down p) := by
    intro p i j hij
    dsimp [down]
    split_ifs <;> omega
  have hsame : ∀ p i, i ≠ p → down p i = up p i := by
    intro p i hi
    dsimp [down, up]
    split_ifs <;> omega
  have hRange : ∀ n p, p < n →
      (List.range n).flatMap (expand p) = List.range (n + 1) := by
    intro n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hp
      by_cases hpn : p = n
      · subst p
        have hpre : (List.range n).flatMap (expand n) = List.range n := by
          calc
            _ = (List.range n).flatMap (fun i ↦ [i]) := by
              apply List.flatMap_congr
              intro i hi
              have hin := List.mem_range.mp hi
              simp [expand, up, hin, Nat.ne_of_lt hin]
            _ = _ := List.flatMap_singleton' _
        simp only [Nat.succ_eq_add_one, List.range_succ, List.flatMap_append,
          List.flatMap_singleton]
        rw [hpre]
        simp [expand, List.append_assoc]
      · have hpn' : p < n := by omega
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih p hpn']
        have hnp : n ≠ p := by omega
        have hnp' : ¬ n < p := by omega
        simp [expand, up, hnp, hnp', List.range_succ]
  have hFlatFilter : ∀ (A : List ℕ) (p : ℕ) (P Q : ℕ → Bool),
      (∀ i ∈ A, ∀ j ∈ expand p i, P j = Q i) →
      (A.flatMap (expand p)).filter P = (A.filter Q).flatMap (expand p) := by
    intro A p P Q
    induction A with
    | nil => intro h; rfl
    | cons i A ih =>
      intro h
      have hchunk : (expand p i).filter P = (expand p i).filter (fun _ ↦ Q i) :=
        List.filter_congr (fun j hj ↦ h i (List.mem_cons_self ..) j hj)
      have hrest := ih (fun j hj ↦ h j (List.mem_cons_of_mem _ hj))
      simp only [List.flatMap_cons, List.filter_append]
      rw [hchunk, hrest]
      cases hq : Q i <;> simp [hq]
  have hFlatMap : ∀ (A : List ℕ) (p : ℕ), p ∉ A →
      A.flatMap (expand p) = A.map (up p) := by
    intro A p hp
    rw [List.map_eq_flatMap]
    apply List.flatMap_congr
    intro i hi
    have hip : i ≠ p := by rintro rfl; exact hp hi
    simp [expand, hip]
  have hHead : ∀ (A : List ℕ) (p : ℕ),
      (A.flatMap (expand p)).head? = A.head?.map (down p) := by
    intro A p
    cases A with
    | nil => rfl
    | cons i A =>
      by_cases hip : i = p
      · subst i; simp [expand, down]
      · simp [List.flatMap_cons, expand, hip, hsame p i hip]
  have hLast : ∀ (A : List ℕ) (p : ℕ),
      (A.flatMap (expand p)).getLast? = A.getLast?.map (up p) := by
    intro A p
    induction A with
    | nil => rfl
    | cons i A ih =>
      have hcons : (i :: A).getLast? = A.getLast?.or (some i) := by
        simpa using (List.getLast?_append (l := [i]) (l' := A))
      rw [List.flatMap_cons, List.getLast?_append, ih, hcons, Option.map_or]
      congr 1
      by_cases hip : i = p
      · subst i; simp [expand, up]
      · simp [expand, hip]
  have hLeftChunk : ∀ p e i, (i = p → e ≠ p) →
      (expand p i).filter (fun j ↦ decide (j < up p e)) =
        if i < e then expand p i else [] := by
    intro p e i h
    by_cases hip : i = p
    · subst i
      have hep := h rfl
      by_cases hpe : p < e
      · have he : ¬ e < p := by omega
        have h1 : p < e + 1 := by omega
        have h2 : p + 1 < e + 1 := by omega
        simp [expand, up, hpe, he, h1, h2] <;> omega
      · have he : e < p := by omega
        have h1 : ¬ p < e := by omega
        have h2 : ¬ p + 1 < e := by omega
        simp [expand, up, he, h1, h2]
    · have hlt : up p i < up p e ↔ i < e := (hup p).lt_iff_lt
      simp only [expand, if_neg hip, List.filter_cons, List.filter_nil, hlt, decide_eq_true_eq]
  have hRightChunk : ∀ p e i, (i = p → e ≠ p) →
      (expand p i).filter (fun j ↦ decide (down p e < j)) =
        if e < i then expand p i else [] := by
    intro p e i h
    by_cases hip : i = p
    · subst i
      have hep := h rfl
      by_cases hep' : e < p
      · have he : e ≤ p := by omega
        have he' : e < p + 1 := by omega
        simp [expand, down, hep', he, he']
      · have he : ¬ e ≤ p := by omega
        have h1 : ¬ e + 1 < p := by omega
        have h2 : ¬ e + 1 < p + 1 := by omega
        simp [expand, down, hep', he, h1, h2]
    · have hlt : down p e < up p i ↔ e < i := by
        rw [← hsame p i hip]
        exact (hdown p).lt_iff_lt
      simp only [expand, if_neg hip, List.filter_cons, List.filter_nil, hlt, decide_eq_true_eq]
  have hLeftSelect : ∀ (A : List ℕ) p e, (p ∈ A → e ≠ p) →
      ((A.flatMap (expand p)).filter (fun j ↦ decide (j < up p e))).getLast? =
        ((A.filter (fun j ↦ decide (j < e))).getLast?).map (up p) := by
    intro A p e h
    have hf : (A.flatMap (expand p)).filter (fun j ↦ decide (j < up p e)) =
        (A.filter (fun j ↦ decide (j < e))).flatMap (expand p) := by
      induction A with
      | nil => rfl
      | cons i A ih =>
        simp only [List.flatMap_cons, List.filter_append]
        rw [hLeftChunk p e i (fun heq ↦ h (by simp [heq])),
          ih (fun hp ↦ h (List.mem_cons_of_mem _ hp))]
        by_cases hie : i < e <;> simp [hie]
    rw [hf, hLast]
  have hRightSelect : ∀ (A : List ℕ) p e, (p ∈ A → e ≠ p) →
      ((A.flatMap (expand p)).filter (fun j ↦ decide (down p e < j))).head? =
        ((A.filter (fun j ↦ decide (e < j))).head?).map (down p) := by
    intro A p e h
    have hf : (A.flatMap (expand p)).filter (fun j ↦ decide (down p e < j)) =
        (A.filter (fun j ↦ decide (e < j))).flatMap (expand p) := by
      induction A with
      | nil => rfl
      | cons i A ih =>
        simp only [List.flatMap_cons, List.filter_append]
        rw [hRightChunk p e i (fun heq ↦ h (by simp [heq])),
          ih (fun hp ↦ h (List.mem_cons_of_mem _ hp))]
        by_cases hie : e < i <;> simp [hie]
    rw [hf, hHead]
  have hGeometry : ∀ (big small : Ctx.Context) (p level : ℕ) (s : Ctx.Side),
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Ctx.Letter.ext level s →
      big.letterAt p = Ctx.Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.childPositions = small.childPositions.map (up p) ∧
      (∀ N, big.extPositions N = (small.extPositions N).flatMap (expand p)) ∧
      big.numRuns = small.numRuns ∧ ∀ N, big.sideAt N = small.sideAt N := by
    intro big small p level s hlen hp hsp hbp hletter
    have hexpand : ∀ i, i < small.word.length → ∀ j ∈ expand p i,
        big.letterAt j = small.letterAt i := by
      intro i hi j hj
      by_cases hip : i = p
      · subst i
        simp only [expand, if_pos rfl, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hbp.trans hsp.symm
        · simpa [up] using hletter p hp
      · simp only [expand, if_neg hip, List.mem_singleton] at hj
        subst j
        exact hletter i hi
    have hchildren : big.childPositions = small.childPositions.map (up p) := by
      unfold Ctx.Context.childPositions
      rw [hlen, ← hRange _ p hp]
      rw [hFlatFilter (List.range small.word.length) p
        (fun j ↦ decide (big.letterAt j = Ctx.Letter.child))
        (fun i ↦ decide (small.letterAt i = Ctx.Letter.child))
        (fun i hi j hj ↦ congrArg
          (fun letter : Ctx.Letter ↦ decide (letter = Ctx.Letter.child))
          (hexpand i (List.mem_range.mp hi) j hj))]
      apply hFlatMap
      simp [hsp]
    have hexternals : ∀ N,
        big.extPositions N = (small.extPositions N).flatMap (expand p) := by
      intro N
      unfold Ctx.Context.extPositions
      rw [hlen, ← hRange _ p hp]
      apply hFlatFilter
      intro i hi j hj
      rw [hexpand i (List.mem_range.mp hi) j hj]
    have hruns : big.numRuns = small.numRuns := by
      let pred (c : Ctx.Context) (i : ℕ) := decide
        (c.letterAt i = Ctx.Letter.child ∧
          (i = 0 ∨ c.letterAt (i - 1) ≠ Ctx.Letter.child))
      have hpred : ∀ i ∈ List.range small.word.length, ∀ j ∈ expand p i,
          pred big j = pred small i := by
        intro i hi j hj
        have hin := List.mem_range.mp hi
        by_cases hip : i = p
        · subst i
          simp [pred, hexpand p hp j hj, hsp]
        · simp only [expand, if_neg hip, List.mem_singleton] at hj
          subst j
          by_cases hi0 : i = 0
          · subst i
            have hp0 : 0 < p := by omega
            have hzero : big.letterAt 0 = small.letterAt 0 := by
              simpa [up, hp0] using hletter 0 hin
            simp [pred, up, hp0, hzero]
          · have hprev : up p (i - 1) = up p i - 1 := by
              dsimp [up]
              split_ifs <;> omega
            have hprevn : i - 1 < small.word.length := by omega
            have hup0 : up p i ≠ 0 := by
              have hmono := hup p (Nat.pos_of_ne_zero hi0)
              exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hmono)
            simp only [pred, hletter i hin, hup0, hi0, false_or]
            rw [← hprev, hletter (i - 1) hprevn]
      change ((List.range big.word.length).filter (pred big)).length =
        ((List.range small.word.length).filter (pred small)).length
      rw [hlen, ← hRange _ p hp, hFlatFilter _ p _ _ hpred]
      have hnot : p ∉ (List.range small.word.length).filter (pred small) := by
        simp [pred, hsp]
      rw [hFlatMap _ p hnot, List.length_map]
    refine ⟨hchildren, hexternals, hruns, ?_⟩
    intro N
    unfold Ctx.Context.sideAt
    rw [hexternals, hHead]
    cases hh : (small.extPositions N).head? with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      have hqmem := List.mem_of_mem_head? hh
      have hqn : q < small.word.length :=
        List.mem_range.mp (List.mem_filter.mp hqmem).1
      by_cases hqp : q = p
      · subst q
        simp [down, hbp, hsp]
      · rw [hsame p q hqp, hletter q hqn]
  have hFolds : ∀ (big small : Ctx.Context) p level s,
      small.letterAt p = Ctx.Letter.ext level s →
      (∀ N, big.extPositions N = (small.extPositions N).flatMap (expand p)) →
      ∀ (ls : List ℕ), ls.Nodup → ∀ e c, (level ∈ ls → e ≠ p) →
      (ls.foldl (Ctx.Context.leftStep big) (up p e, c)).2 =
          (ls.foldl (Ctx.Context.leftStep small) (e, c)).2 ∧
      (ls.foldl (Ctx.Context.rightStep big) (down p e, c)).2 =
          (ls.foldl (Ctx.Context.rightStep small) (e, c)).2 := by
    intro big small p level s hsp hext
    have htag : ∀ N, p ∈ small.extPositions N → N = level := by
      intro N hmem
      have h := (List.mem_filter.mp hmem).2
      simpa [hsp, eq_comm] using h
    intro ls
    induction ls with
    | nil => intro hn e c he; exact ⟨rfl, rfl⟩
    | cons N ls ih =>
      intro hn e c he
      have hn' := List.nodup_cons.mp hn
      have hguard : p ∈ small.extPositions N → e ≠ p := by
        intro hp
        apply he
        rw [← htag N hp]
        exact List.mem_cons_self ..
      have hrest : level ∈ ls → e ≠ p := fun hl ↦ he (List.mem_cons_of_mem _ hl)
      have hnext : ∀ q, q ∈ small.extPositions N → level ∈ ls → q ≠ p := by
        intro q hq hl hqp
        subst q
        exact hn'.1 ((htag N hq).symm ▸ hl)
      constructor
      · have hs := hLeftSelect (small.extPositions N) p e hguard
        rw [← hext N] at hs
        simp only [List.foldl_cons, Ctx.Context.leftStep]
        rw [hs]
        cases hq : ((small.extPositions N).filter (fun j ↦ decide (j < e))).getLast? with
        | none =>
          simp only [Option.map_none]
          exact (ih hn'.2 e c hrest).1
        | some q =>
          simp only [Option.map_some]
          have hqm := (List.mem_filter.mp (List.mem_of_mem_getLast? hq)).1
          exact (ih hn'.2 q (c + 1) (hnext q hqm)).1
      · have hs := hRightSelect (small.extPositions N) p e hguard
        rw [← hext N] at hs
        simp only [List.foldl_cons, Ctx.Context.rightStep]
        rw [hs]
        cases hq : ((small.extPositions N).filter (fun j ↦ decide (e < j))).head? with
        | none =>
          simp only [Option.map_none]
          exact (ih hn'.2 e c hrest).2
        | some q =>
          simp only [Option.map_some]
          have hqm := (List.mem_filter.mp (List.mem_of_mem_head? hq)).1
          exact (ih hn'.2 q (c + 1) (hnext q hqm)).2
  have hLevelsNodup : ∀ (c : Ctx.Context) s top, (c.levelsOn s top).Nodup := by
    intro c s top
    unfold Ctx.Context.levelsOn
    apply List.Nodup.filter
    unfold Ctx.Context.levels
    exact (List.nodup_range (n := c.maxima.length)).map (fun x y h ↦ Nat.add_right_cancel h)
  have hBase : ∀ (big small : Ctx.Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Ctx.Letter.ext level s →
      big.letterAt p = Ctx.Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.base = small.base := by
    intro big small p level s ha hu hk hm hlen hp hsp hbp hletter
    obtain ⟨hchildren, hexternals, hruns, hsides⟩ :=
      hGeometry big small p level s hlen hp hsp hbp hletter
    have hlevels : ∀ s top, big.levelsOn s top = small.levelsOn s top := by
      intro s top
      unfold Ctx.Context.levelsOn Ctx.Context.levels
      rw [hm]
      apply List.filter_congr
      intro N hN
      rw [hsides N]
    have hExt : ∀ s top e, e ≠ p →
        big.leftExt s top (up p e) = small.leftExt s top e ∧
        big.rightExt s top (up p e) = small.rightExt s top e := by
      intro t top e hep
      have hmap : ∀ ls ∈ (small.levelsOn t top).sublists,
          (ls.foldl (Ctx.Context.leftStep big) (up p e, 0)).2 =
            (ls.foldl (Ctx.Context.leftStep small) (e, 0)).2 ∧
          (ls.foldl (Ctx.Context.rightStep big) (up p e, 0)).2 =
            (ls.foldl (Ctx.Context.rightStep small) (e, 0)).2 := by
        intro ls hls
        have hnd := (hLevelsNodup small t top).sublist (List.mem_sublists.mp hls)
        simpa [hsame p e hep] using hFolds big small p level s hsp hexternals
          ls hnd e 0 (fun _ ↦ hep)
      constructor
      · rw [Ctx.Context.leftExt_eq, Ctx.Context.leftExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).1)
      · rw [Ctx.Context.rightExt_eq, Ctx.Context.rightExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hmap ls hls).2)
    have hchain : ∀ s e, e ≠ p →
        big.chainExt s (up p e) (up p e) = small.chainExt s e e := by
      intro t e he
      unfold Ctx.Context.chainExt
      rw [(hExt t 0 e he).1, (hExt t 0 e he).2]
    have hjoin : ∀ s e, e ≠ p →
        big.joinExt s (up p e) (up p e) = small.joinExt s e e := by
      intro t e he
      unfold Ctx.Context.joinExt
      rw [hchain t e he, hlevels]
      congr 3
      apply List.map_congr_left
      intro N hN
      rw [(hExt t N e he).1, (hExt t N e he).2]
      simp [Ctx.Context.maximumAt, hm]
    unfold Ctx.Context.base
    rw [hchildren, List.head?_map]
    cases hh : small.childPositions.head? with
    | none => rfl
    | some e =>
      simp only [Option.map_some]
      have hep : e ≠ p := by
        intro hep
        have hmem := List.mem_of_mem_head? hh
        have h := (List.mem_filter.mp hmem).2
        simp [hep, hsp] at h
      have hcl : big.cupLimit (up p e) (up p e) = small.cupLimit e e := by
        unfold Ctx.Context.cupLimit
        rw [hu, hk, hchain _ e hep, hjoin _ e hep]
      have hpl : big.capLimit (up p e) (up p e) = small.capLimit e e := by
        unfold Ctx.Context.capLimit
        rw [ha, hk, hchain _ e hep, hjoin _ e hep]
      rw [hcl, hpl, hk]
  have hMapMem : ∀ p (A : List ℕ) i, up p i ∈ A.map (up p) ↔ i ∈ A := by
    intro p A i
    constructor
    · intro h
      obtain ⟨j, hj, heq⟩ := List.mem_map.mp h
      have hji := (hup p).injective heq
      simpa [hji] using hj
    · exact List.mem_map_of_mem
  have hRest : ∀ p (A B : List ℕ),
      (A.map (up p)).filter (fun i ↦ decide (i ∉ B.map (up p))) =
        (A.filter (fun i ↦ decide (i ∉ B))).map (up p) := by
    intro p A B
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    change decide (up p i ∉ B.map (up p)) = decide (i ∉ B)
    simp only [hMapMem p B i]
  have hBlocks : ∀ (big small : Ctx.Context) p,
      big.childPositions = small.childPositions.map (up p) →
      big.blocks = small.blocks.map (fun B ↦ B.map (up p)) := by
    intro big small p hc
    simp only [Ctx.Context.blocks, hc]
    simp only [List.length_map]
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
      simp [Function.comp_def, List.map_take, List.map_drop]
    rw [hraw, List.filter_map]
    congr 1
    apply List.filter_congr
    intro B hB
    simp [Function.comp_def]
  have hFuel : ∀ fuel (big small : Ctx.Context) p level s,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Ctx.Letter.ext level s →
      big.letterAt p = Ctx.Letter.ext level s →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      Ctx.Context.boundFuel fuel big = Ctx.Context.boundFuel fuel small := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro big small p level s ha hu hk hm hlen hp hsp hbp hletter
      obtain ⟨hc, hext, hruns, hsides⟩ :=
        hGeometry big small p level s hlen hp hsp hbp hletter
      have hparts : ∀ (B : List ℕ) (t : Ctx.Side) m,
          Ctx.Context.boundFuel fuel (big.part (B.map (up p)) t m) =
            Ctx.Context.boundFuel fuel (small.part B t m) := by
        intro B t m
        have hpbig : p < big.word.length := by omega
        apply ih (big.part (B.map (up p)) t m) (small.part B t m) p (level + 1) s
        · exact ha
        · exact hu
        · exact hk
        · simp [Ctx.Context.part, hm]
        · simpa only [Ctx.Context.part_word_length] using hlen
        · simpa only [Ctx.Context.part_word_length] using hp
        · exact Ctx.Context.part_letterAt_of_ext small B t m hp hsp
        · exact Ctx.Context.part_letterAt_of_ext big (B.map (up p)) t m hpbig hbp
        · intro i hi
          have his : i < small.word.length := by
            simpa only [Ctx.Context.part_word_length] using hi
          have hib : up p i < big.word.length := by
            rw [hlen]
            dsimp [up]
            split_ifs <;> omega
          cases hs : small.letterAt i with
          | child =>
            rw [Ctx.Context.part_letterAt_of_child big (B.map (up p)) t m hib
              ((hletter i his).trans hs), Ctx.Context.part_letterAt_of_child small B t m his hs]
            simp [hMapMem]
          | ext N t' =>
            rw [Ctx.Context.part_letterAt_of_ext big (B.map (up p)) t m hib
              ((hletter i his).trans hs), Ctx.Context.part_letterAt_of_ext small B t m his hs]
      rw [Ctx.Context.boundFuel.eq_2, Ctx.Context.boundFuel.eq_2, hruns]
      by_cases hrun : small.numRuns ≤ 1
      · simp only [if_pos hrun]
        exact hBase big small p level s ha hu hk hm hlen hp hsp hbp hletter
      · simp only [if_neg hrun]
        rw [hc, hBlocks big small p hc, hk, List.flatMap_map]
        congr 2
        apply List.flatMap_congr
        intro B hB
        rw [hRest]
        apply List.flatMap_congr
        intro d hd
        rw [hparts B Ctx.Side.lower (d + 1),
          hparts (small.childPositions.filter (fun q ↦ decide (q ∉ B))) Ctx.Side.upper
            (small.k - 1 - (d + 1)),
          hparts B Ctx.Side.upper (small.k - 1 - (d + 1)),
          hparts (small.childPositions.filter (fun q ↦ decide (q ∉ B))) Ctx.Side.lower (d + 1)]
  let small : Ctx.Context := { σ with word := left ++ [Ctx.Letter.ext lev side] ++ right }
  let p := left.length
  have hsw : small.word = left ++ Ctx.Letter.ext lev side :: right := by
    simp [small, List.append_assoc]
  have hbw : σ.word = left ++ Ctx.Letter.ext lev side :: Ctx.Letter.ext lev side :: right := by
    simpa [List.append_assoc] using hword
  have hp : p < small.word.length := by simp [p, hsw]
  have hlen : σ.word.length = small.word.length + 1 := by simp [hsw, hbw]; omega
  have hsp : small.letterAt p = Ctx.Letter.ext lev side := by
    unfold Ctx.Context.letterAt
    rw [hsw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hbp : σ.letterAt p = Ctx.Letter.ext lev side := by
    unfold Ctx.Context.letterAt
    rw [hbw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hletter : ∀ i, i < small.word.length → σ.letterAt (up p i) = small.letterAt i := by
    intro i hi
    by_cases hip : i < p
    · have hil : i < left.length := hip
      simp only [up, if_pos hip, Ctx.Context.letterAt, hsw, hbw,
        List.getElem?_append_left hil]
    · have hpi : left.length ≤ i := Nat.le_of_not_gt hip
      have hpi' : left.length ≤ i + 1 := by omega
      have hsub : i + 1 - left.length = (i - left.length) + 1 := by omega
      simp only [up, if_neg hip, Ctx.Context.letterAt, hsw, hbw,
        List.getElem?_append_right hpi', List.getElem?_append_right hpi,
        hsub, List.getElem?_cons_succ]
  have hc := (hGeometry σ small p lev side hlen hp hsp hbp hletter).1
  change Ctx.Context.boundFuel (σ.childPositions.length + 1) σ =
    Ctx.Context.boundFuel (small.childPositions.length + 1) small
  rw [hc, List.length_map]
  exact hFuel _ σ small p lev side rfl rfl rfl rfl hlen hp hsp hbp hletter

end ErdosSzekeres
