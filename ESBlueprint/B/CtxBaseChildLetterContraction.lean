import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- Deleting one of two adjacent child letters preserves the base value. This positional transport helper supports the uniform-separator and three-block contraction reductions; it asserts equality of bases only, since unrestricted recursive bound contraction is false.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_base_child_letter_contraction (σ : Ctx.Context) (left right : List Ctx.Letter)
  (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) :
  σ.base = ({ σ with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).base := by
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
  have hMapDown : ∀ (A : List ℕ) p, p ∉ A →
      A.flatMap (expand p) = A.map (down p) := by
    intro A p hp
    rw [hFlatMap A p hp]
    apply List.map_congr_left
    intro i hi
    exact (hsame p i (fun h ↦ hp (h ▸ hi))).symm
  have hSelectors : ∀ (A : List ℕ) p e,
      ((A.map (down p)).filter (fun j ↦ decide (j < down p e))).getLast? =
        ((A.filter (fun j ↦ decide (j < e))).getLast?).map (down p) ∧
      ((A.map (down p)).filter (fun j ↦ decide (down p e < j))).head? =
        ((A.filter (fun j ↦ decide (e < j))).head?).map (down p) := by
    intro A p e
    have hleft : (A.map (down p)).filter (fun j ↦ decide (j < down p e)) =
        (A.filter (fun j ↦ decide (j < e))).map (down p) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro i hi
      simp only [Function.comp_apply, (hdown p).lt_iff_lt]
    have hright : (A.map (down p)).filter (fun j ↦ decide (down p e < j)) =
        (A.filter (fun j ↦ decide (e < j))).map (down p) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro i hi
      simp only [Function.comp_apply, (hdown p).lt_iff_lt]
    constructor
    · rw [hleft, List.getLast?_map]
    · rw [hright, List.head?_map]
  have hBase : ∀ (big small : Ctx.Context) p,
      big.a = small.a → big.u = small.u → big.k = small.k → big.maxima = small.maxima →
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Ctx.Letter.child → big.letterAt p = Ctx.Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.base = small.base := by
    intro big small p ha hu hk hm hlen hp hsp hbp hletter
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
    have hletterDown : ∀ i, i < small.word.length →
        big.letterAt (down p i) = small.letterAt i := by
      intro i hi
      by_cases hip : i = p
      · subst i; simpa [down] using hbp.trans hsp.symm
      · rw [hsame p i hip, hletter i hi]
    have hchildren : big.childPositions = small.childPositions.flatMap (expand p) := by
      unfold Ctx.Context.childPositions
      rw [hlen, ← hRange _ p hp]
      apply hFlatFilter
      intro i hi j hj
      rw [hexpand i (List.mem_range.mp hi) j hj]
    have hexternals : ∀ N, big.extPositions N = (small.extPositions N).map (down p) := by
      intro N
      have hnot : p ∉ small.extPositions N := by
        simp [Ctx.Context.extPositions, hsp]
      rw [← hMapDown _ p hnot]
      unfold Ctx.Context.extPositions
      rw [hlen, ← hRange _ p hp]
      apply hFlatFilter
      intro i hi j hj
      rw [hexpand i (List.mem_range.mp hi) j hj]
    have hsides : ∀ N, big.sideAt N = small.sideAt N := by
      intro N
      unfold Ctx.Context.sideAt
      rw [hexternals, List.head?_map]
      cases hh : (small.extPositions N).head? with
      | none => rfl
      | some i =>
        have hi := List.mem_of_mem_head? hh
        have hir : i < small.word.length := List.mem_range.mp (List.mem_filter.mp hi).1
        simp only [Option.map_some]
        rw [hletterDown i hir]
    have hlevels : ∀ s top, big.levelsOn s top = small.levelsOn s top := by
      intro s top
      unfold Ctx.Context.levelsOn Ctx.Context.levels
      rw [hm]
      apply List.filter_congr
      intro N hN
      rw [hsides N]
    have hFolds : ∀ (ls : List ℕ) e c,
        (ls.foldl (Ctx.Context.leftStep big) (down p e, c)).2 =
          (ls.foldl (Ctx.Context.leftStep small) (e, c)).2 ∧
        (ls.foldl (Ctx.Context.rightStep big) (down p e, c)).2 =
          (ls.foldl (Ctx.Context.rightStep small) (e, c)).2 := by
      intro ls
      induction ls with
      | nil => intro e c; exact ⟨rfl, rfl⟩
      | cons N ls ih =>
        intro e c
        constructor
        · simp only [List.foldl_cons, Ctx.Context.leftStep]
          rw [hexternals N, (hSelectors _ p e).1]
          cases hq : ((small.extPositions N).filter (fun j ↦ decide (j < e))).getLast? with
          | none => exact (ih e c).1
          | some q => exact (ih q (c + 1)).1
        · simp only [List.foldl_cons, Ctx.Context.rightStep]
          rw [hexternals N, (hSelectors _ p e).2]
          cases hq : ((small.extPositions N).filter (fun j ↦ decide (e < j))).head? with
          | none => exact (ih e c).2
          | some q => exact (ih q (c + 1)).2
    have hExt : ∀ s top e,
        big.leftExt s top (down p e) = small.leftExt s top e ∧
        big.rightExt s top (down p e) = small.rightExt s top e := by
      intro s top e
      constructor
      · rw [Ctx.Context.leftExt_eq, Ctx.Context.leftExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hFolds ls e 0).1)
      · rw [Ctx.Context.rightExt_eq, Ctx.Context.rightExt_eq, hlevels]
        congr 2
        exact List.map_congr_left (fun ls hls ↦ (hFolds ls e 0).2)
    have hchain : ∀ s e,
        big.chainExt s (down p e) (down p e) = small.chainExt s e e := by
      intro s e
      unfold Ctx.Context.chainExt
      rw [(hExt s 0 e).1, (hExt s 0 e).2]
    have hjoin : ∀ s e,
        big.joinExt s (down p e) (down p e) = small.joinExt s e e := by
      intro s e
      unfold Ctx.Context.joinExt
      rw [hchain s e, hlevels]
      congr 3
      apply List.map_congr_left
      intro N hN
      rw [(hExt s N e).1, (hExt s N e).2]
      simp [Ctx.Context.maximumAt, hm]
    unfold Ctx.Context.base
    rw [hchildren, hHead]
    cases hh : small.childPositions.head? with
    | none => rfl
    | some e =>
      simp only [Option.map_some]
      have hcl : big.cupLimit (down p e) (down p e) = small.cupLimit e e := by
        unfold Ctx.Context.cupLimit
        rw [hu, hk, hchain, hjoin]
      have hpl : big.capLimit (down p e) (down p e) = small.capLimit e e := by
        unfold Ctx.Context.capLimit
        rw [ha, hk, hchain, hjoin]
      rw [hcl, hpl, hk]
  let small : Ctx.Context := { σ with word := left ++ [Ctx.Letter.child] ++ right }
  let p := left.length
  have hsw : small.word = left ++ Ctx.Letter.child :: right := by
    simp [small, List.append_assoc]
  have hbw : σ.word = left ++ Ctx.Letter.child :: Ctx.Letter.child :: right := by
    simpa [List.append_assoc] using hword
  have hp : p < small.word.length := by simp [p, hsw]
  have hlen : σ.word.length = small.word.length + 1 := by simp [hsw, hbw]; omega
  have hsp : small.letterAt p = Ctx.Letter.child := by
    unfold Ctx.Context.letterAt
    rw [hsw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hbp : σ.letterAt p = Ctx.Letter.child := by
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
  exact hBase σ small p rfl rfl rfl rfl hlen hp hsp hbp hletter

end ErdosSzekeres
