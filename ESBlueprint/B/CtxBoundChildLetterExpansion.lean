import ESBlueprint.B.CtxBoundAdditiveThreeBlocksOfUniformContraction

import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 4000000

/-- Duplicating a child letter cannot decrease the recursive context bound, for arbitrary well-formed contexts. Lift an interval cut by keeping both copies together; recursive parts either duplicate a child or duplicate an external letter. This supplies one inequality in the approved uniform-separator one-step contraction, while equality for unrestricted contexts is false.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_base_child_letter_contraction, ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_child_letter_expansion (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter)
  (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) :
  ({ σ with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound ≤ σ.bound := by
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
  have hFlatMem : ∀ p (A : List ℕ) i j, j ∈ expand p i →
      (j ∈ A.flatMap (expand p) ↔ i ∈ A) := by
    have hdisjoint : ∀ p i j x, x ∈ expand p i → x ∈ expand p j → i = j := by
      intro p i j x hi hj
      dsimp [expand, up] at hi hj
      split_ifs at hi hj <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton] at hi hj <;>
        omega
    intro p A i j hji
    constructor
    · intro hj
      obtain ⟨i', hi', hj'⟩ := List.mem_flatMap.mp hj
      exact (hdisjoint p i' i j hj' hji) ▸ hi'
    · intro hi
      exact List.mem_flatMap.mpr ⟨i, hi, hji⟩
  have hUpMem : ∀ p i, up p i ∈ expand p i := by
    intro p i
    by_cases h : i = p <;> simp [expand, up, h]
  have hDownMem : ∀ p i, down p i ∈ expand p i := by
    intro p i
    by_cases h : i = p
    · simp [expand, down, h]
    · simpa [hsame p i h] using hUpMem p i
  have hRest : ∀ p (A B : List ℕ),
      (A.flatMap (expand p)).filter (fun i ↦ decide (i ∉ B.flatMap (expand p))) =
        (A.filter (fun i ↦ decide (i ∉ B))).flatMap (expand p) := by
    intro p A B
    apply hFlatFilter
    intro i hi j hj
    simp only [hFlatMem p B i j hj]
  have hStruct : ∀ (big small : Context), big.a = small.a → big.u = small.u →
      big.k = small.k → big.maxima = small.maxima →
      ({ big with word := small.word } : Context) = small := by
    intro big small ha hu hk hm
    cases big; cases small
    simp_all
  have hWords : ∀ (big small : Context) p,
      big.word.length = small.word.length + 1 → p < small.word.length →
      big.letterAt p = small.letterAt p →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.word = small.word.take p ++ [small.letterAt p, small.letterAt p] ++
        small.word.drop (p + 1) ∧
      small.word = small.word.take p ++ [small.letterAt p] ++ small.word.drop (p + 1) := by
    intro big small p hlen hp hbp hletter
    have hget : ∀ (c : Context) i, i < c.word.length → c.word[i]? = some (c.letterAt i) := by
      intro c i hi
      simp [Context.letterAt, List.getElem?_eq_getElem hi]
    have htake : big.word.take p = small.word.take p := by
      apply List.ext_getElem (by simp; omega)
      intro i hi hj
      have hip : i < p := by simp only [List.length_take] at hi; omega
      have his : i < small.word.length := by omega
      have hib : i < big.word.length := by omega
      have hh := hletter i his
      simpa [up, hip, Context.letterAt, List.getElem?_eq_getElem his,
        List.getElem?_eq_getElem hib] using hh
    have hdrop : big.word.drop (p + 2) = small.word.drop (p + 1) := by
      apply List.ext_getElem (by simp; omega)
      intro i hi hj
      have his : p + 1 + i < small.word.length := by
        simp only [List.length_drop] at hj; omega
      have hib : p + 2 + i < big.word.length := by omega
      have hh := hletter (p + 1 + i) his
      have hnot : ¬ p + 1 + i < p := by omega
      have he : p + 1 + i + 1 = p + 2 + i := by omega
      simpa [up, hnot, he, Context.letterAt, List.getElem?_eq_getElem his,
        List.getElem?_eq_getElem hib] using hh
    have hb0 : big.word[p]? = some (small.letterAt p) := by
      rw [hget big p (by omega), hbp]
    have hb1 : big.word[p + 1]? = some (small.letterAt p) := by
      have h : big.letterAt (p + 1) = small.letterAt p := by simpa [up] using hletter p hp
      exact (hget big (p + 1) (by omega)).trans (congrArg some h)
    constructor
    · calc
        big.word = big.word.take (p + 2) ++ big.word.drop (p + 2) :=
          (List.take_append_drop _ _).symm
        _ = _ := by
          rw [show p + 2 = (p + 1) + 1 by omega, List.take_add_one, List.take_add_one,
            hb0, hb1, htake]
          simpa [List.append_assoc] using congrArg
            (fun R ↦ small.word.take p ++ [small.letterAt p, small.letterAt p] ++ R) hdrop
    · calc
        small.word = small.word.take (p + 1) ++ small.word.drop (p + 1) :=
          (List.take_append_drop _ _).symm
        _ = _ := by rw [List.take_add_one, hget small p hp]; rfl
  have hGeometry : ∀ (big small : Context) p,
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Letter.child → big.letterAt p = Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.childPositions = small.childPositions.flatMap (expand p) ∧
      big.numRuns = small.numRuns := by
    intro big small p hlen hp hsp hbp hletter
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
    constructor
    · unfold Context.childPositions
      rw [hlen, ← hRange _ p hp]
      apply hFlatFilter
      intro i hi j hj
      rw [hexpand i (List.mem_range.mp hi) j hj]
    · let pred (c : Context) (i : ℕ) := decide
        (c.letterAt i = Letter.child ∧ (i = 0 ∨ c.letterAt (i - 1) ≠ Letter.child))
      have hfirst : ∀ i, i < small.word.length → pred big (down p i) = pred small i := by
        intro i hi
        have hlet := hexpand i hi (down p i) (hDownMem p i)
        by_cases hi0 : i = 0
        · subst i
          have hd0 : down p 0 = 0 := by simp [down]
          simp [pred, hd0] at hlet ⊢
          exact congrArg (fun x ↦ x = Letter.child) hlet |>.to_iff
        · have hprev : up p (i - 1) = down p i - 1 := by
            dsimp [up, down]; split_ifs <;> omega
          have hd0 : down p i ≠ 0 := Nat.ne_of_gt
            (lt_of_le_of_lt (Nat.zero_le _) (hdown p (Nat.pos_of_ne_zero hi0)))
          simp only [pred, hlet, hd0, hi0, false_or]
          rw [← hprev, hletter (i - 1) (by omega)]
      have hsecond : pred big (p + 1) = false := by
        have hpred : (p + 1) - 1 = p := by omega
        simp [pred, hpred, hbp]
      have hchunk : ∀ i ∈ List.range small.word.length,
          (expand p i).filter (pred big) = if pred small i then [down p i] else [] := by
        intro i hi
        have hh := hfirst i (List.mem_range.mp hi)
        by_cases hip : i = p
        · subst i
          simp only [down, Nat.le_refl, if_true] at hh
          simp only [expand, if_pos rfl, List.filter_cons, List.filter_nil, hsecond,
            Bool.false_eq_true, if_false, hh, down, Nat.le_refl, if_true]
        · have he := hsame p i hip
          simp only [expand, if_neg hip, List.filter_cons, List.filter_nil, ← he, hh]
      have hfiltered : ((List.range small.word.length).flatMap (expand p)).filter (pred big) =
          ((List.range small.word.length).filter (pred small)).map (down p) := by
        rw [List.filter_flatMap]
        have hlist : ∀ A : List ℕ,
            (∀ i ∈ A, (expand p i).filter (pred big) = if pred small i then [down p i] else []) →
            A.flatMap (fun i ↦ (expand p i).filter (pred big)) =
              (A.filter (pred small)).map (down p) := by
          intro A
          induction A with
          | nil => intro _; rfl
          | cons i A ih =>
            intro h
            rw [List.flatMap_cons, h i (List.mem_cons_self ..),
              ih (fun j hj ↦ h j (List.mem_cons_of_mem _ hj))]
            cases he : pred small i <;> simp [he]
        exact hlist _ hchunk
      change ((List.range big.word.length).filter (pred big)).length =
        ((List.range small.word.length).filter (pred small)).length
      rw [hlen, ← hRange _ p hp, hfiltered, List.length_map]
  have hFlatNil : ∀ p (A : List ℕ), A.flatMap (expand p) = [] ↔ A = [] := by
    intro p A
    cases A with
    | nil => simp
    | cons i A =>
      by_cases hip : i = p <;> simp [List.flatMap_cons, expand, hip]
  have hFlatPos : ∀ p (A : List ℕ), A ≠ [] → 0 < (A.flatMap (expand p)).length := by
    intro p A hA
    by_contra h
    have hz : A.flatMap (expand p) = [] := List.length_eq_zero_iff.mp (by omega)
    exact hA ((hFlatNil p A).mp hz)
  have hBlocks : ∀ (big small : Context) p (B : List ℕ),
      big.childPositions = small.childPositions.flatMap (expand p) →
      B ∈ small.blocks → B.flatMap (expand p) ∈ big.blocks := by
    intro big small p B hc hb
    obtain ⟨hblen, hbne, _⟩ := mem_blocks hb
    unfold Context.blocks at hb
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
      decide_eq_true_eq] at hb
    obtain ⟨⟨i, hi, j, hj, hEq⟩, _⟩ := hb
    let A := small.childPositions.take i
    let C := small.childPositions.drop (i + (j + 1))
    have hsplit : small.childPositions = A ++ B ++ C := by
      rw [← hEq]
      dsimp [A, C]
      rw [← List.take_add, List.take_append_drop]
    have hbig : big.childPositions = A.flatMap (expand p) ++ B.flatMap (expand p) ++
        C.flatMap (expand p) := by rw [hc, hsplit]; simp only [List.flatMap_append]
    have hBpos := hFlatPos p B hbne
    have hACpos : 0 < (A.flatMap (expand p)).length + (C.flatMap (expand p)).length := by
      by_cases hA : A = []
      · have hC : C ≠ [] := by
          intro hC
          rw [hsplit, hA, hC] at hblen
          simp at hblen
        have := hFlatPos p C hC
        omega
      · have := hFlatPos p A hA
        omega
    have hlt : (B.flatMap (expand p)).length < big.childPositions.length := by
      rw [hbig]
      simp only [List.length_append]
      omega
    have hstart : (A.flatMap (expand p)).length < big.childPositions.length := by
      rw [hbig]
      simp only [List.length_append]
      omega
    have hlen : (B.flatMap (expand p)).length - 1 <
        big.childPositions.length - (A.flatMap (expand p)).length := by
      rw [hbig]
      simp only [List.length_append]
      omega
    unfold Context.blocks
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
      decide_eq_true_eq]
    refine ⟨⟨(A.flatMap (expand p)).length, hstart,
      (B.flatMap (expand p)).length - 1, hlen, ?_⟩, hlt⟩
    rw [hbig, show (B.flatMap (expand p)).length - 1 + 1 =
      (B.flatMap (expand p)).length by omega]
    simp [List.append_assoc]
  have hPartRel : ∀ (big small : Context) p,
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Letter.child → big.letterAt p = Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      ∀ B s q,
      (big.part (B.flatMap (expand p)) s q).letterAt p = (small.part B s q).letterAt p ∧
      ∀ i, i < (small.part B s q).word.length →
        (big.part (B.flatMap (expand p)) s q).letterAt (up p i) =
          (small.part B s q).letterAt i := by
    intro big small p hlen hp hsp hbp hletter B s q
    constructor
    · rw [part_letterAt_of_child big _ s q (by omega) hbp,
        part_letterAt_of_child small B s q hp hsp]
      have hm := hFlatMem p B p p (by simp [expand])
      simp only [hm]
    · intro i hi
      have his : i < small.word.length := by simpa only [part_word_length] using hi
      have hib : up p i < big.word.length := by
        rw [hlen]; dsimp [up]; split_ifs <;> omega
      cases hs : small.letterAt i with
      | child =>
        rw [part_letterAt_of_child big _ s q hib ((hletter i his).trans hs),
          part_letterAt_of_child small B s q his hs]
        simp only [hFlatMem p B i (up p i) (hUpMem p i)]
      | ext N t =>
        rw [part_letterAt_of_ext big _ s q hib ((hletter i his).trans hs),
          part_letterAt_of_ext small B s q his hs]
  have hGo : ∀ n (big small : Context) p, small.childPositions.length = n →
      big.WellFormed → big.a = small.a → big.u = small.u → big.k = small.k →
      big.maxima = small.maxima → big.word.length = small.word.length + 1 →
      p < small.word.length → small.letterAt p = Letter.child → big.letterAt p = Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      small.bound ≤ big.bound := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro big small p hn hwf ha hu hk hm hlen hp hsp hbp hletter
      obtain ⟨hc, hruns⟩ := hGeometry big small p hlen hp hsp hbp hletter
      have hw := hWords big small p hlen hp (hbp.trans hsp.symm) hletter
      have hsctx : ({ big with
          word := small.word.take p ++ [Letter.child] ++ small.word.drop (p + 1) } : Context) = small := by
        rw [← hsp, ← hw.2]
        exact hStruct big small ha hu hk hm
      by_cases hrun : small.numRuns ≤ 1
      · have hbase := ctx_base_child_letter_contraction big (small.word.take p)
          (small.word.drop (p + 1)) (by simpa only [hsp] using hw.1)
        rw [hsctx] at hbase
        simp [Context.bound, Context.boundFuel, hruns, hrun, hbase]
      · have hrbig : 2 ≤ big.numRuns := by omega
        have hparts : ∀ (B : List ℕ) s q, 1 ≤ q → q ≤ small.k - 2 →
            (small.part B s q).childPositions.length < n →
            (small.part B s q).bound ≤ (big.part (B.flatMap (expand p)) s q).bound := by
          intro B s q hq hqk hless
          let big' := big.part (B.flatMap (expand p)) s q
          let small' := small.part B s q
          have hwf' : big'.WellFormed := hwf.part _ s hq (by simpa [hk] using hqk)
          have hlen' : big'.word.length = small'.word.length + 1 := by
            simpa only [big', small', part_word_length] using hlen
          have hp' : p < small'.word.length := by simpa only [small', part_word_length] using hp
          obtain ⟨hpoint, hletters⟩ := hPartRel big small p hlen hp hsp hbp hletter B s q
          have hsm : small'.letterAt p = if p ∈ B then Letter.child else Letter.ext 1 s :=
            part_letterAt_of_child small B s q hp hsp
          by_cases hmem : p ∈ B
          · have hs' : small'.letterAt p = Letter.child := by simpa [hmem] using hsm
            exact ih small'.childPositions.length hless big' small' p rfl hwf'
              ha hu hk (by simp [big', small', Context.part, hm]) hlen' hp' hs'
              (hpoint.trans hs') hletters
          · have hs' : small'.letterAt p = Letter.ext 1 s := by simpa [hmem] using hsm
            have hwords := hWords big' small' p hlen' hp' hpoint hletters
            have he := ctx_bound_external_letter_contraction big' hwf' (small'.word.take p)
              (small'.word.drop (p + 1)) 1 s (by simpa only [hs'] using hwords.1)
            have hctx : ({ big' with
                word := small'.word.take p ++ [Letter.ext 1 s] ++ small'.word.drop (p + 1) } : Context) = small' := by
              rw [← hs', ← hwords.2]
              exact hStruct big' small' ha hu hk (by simp [big', small', Context.part, hm])
            rw [hctx] at he
            exact he.ge
        unfold Context.bound
        rw [Context.boundFuel.eq_2, if_neg hrun]
        dsimp only
        apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨B, hb, d, hd, hx⟩ := hx
        have hd1 : 1 ≤ d + 1 := by omega
        have hdk : d + 1 ≤ small.k - 2 := by omega
        have hc1 : 1 ≤ small.k - 1 - (d + 1) := by omega
        have hck : small.k - 1 - (d + 1) ≤ small.k - 2 := by omega
        have hbBig := hBlocks big small p B hc hb
        have hcut := ctx_bound_cut_le big hrbig (B.flatMap (expand p)) hbBig (d + 1) hd1
          (by simpa [hk] using hdk)
        rw [hc, hRest p small.childPositions B, hk] at hcut
        have hB : ∀ s q, (small.part B s q).childPositions.length < n := by
          intro s q
          rw [← hn]
          exact part_childPositions_length_lt_of_mem_blocks hb s q
        have hR : ∀ s q,
            (small.part (small.childPositions.filter (fun i ↦ i ∉ B)) s q).childPositions.length < n := by
          intro s q
          rw [← hn]
          exact part_rest_childPositions_length_lt_of_mem_blocks hb s q
        have hfB : ∀ s q,
            boundFuel small.childPositions.length (small.part B s q) = (small.part B s q).bound := by
          intro s q
          apply boundFuel_eq_bound
          have := hB s q
          omega
        have hfR : ∀ s q,
            boundFuel small.childPositions.length
                (small.part (small.childPositions.filter (fun i ↦ i ∉ B)) s q) =
              (small.part (small.childPositions.filter (fun i ↦ i ∉ B)) s q).bound := by
          intro s q
          apply boundFuel_eq_bound
          have := hR s q
          omega
        rcases hx with rfl | rfl
        · rw [hfB, hfR]
          exact (Nat.add_le_add (hparts B Side.lower _ hd1 hdk (hB _ _))
            (hparts _ Side.upper _ hc1 hck (hR _ _))).trans hcut.1
        · rw [hfB, hfR]
          exact (Nat.add_le_add (hparts B Side.upper _ hc1 hck (hB _ _))
            (hparts _ Side.lower _ hd1 hdk (hR _ _))).trans hcut.2
  let small : Context := { σ with word := left ++ [Letter.child] ++ right }
  let p := left.length
  have hsw : small.word = left ++ Letter.child :: right := by simp [small, List.append_assoc]
  have hbw : σ.word = left ++ Letter.child :: Letter.child :: right := by
    simpa [List.append_assoc] using hword
  have hp : p < small.word.length := by simp [p, hsw]
  have hlen : σ.word.length = small.word.length + 1 := by simp [hsw, hbw]; omega
  have hsp : small.letterAt p = Letter.child := by
    unfold Context.letterAt
    rw [hsw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hbp : σ.letterAt p = Letter.child := by
    unfold Context.letterAt
    rw [hbw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hletter : ∀ i, i < small.word.length → σ.letterAt (up p i) = small.letterAt i := by
    intro i hi
    by_cases hip : i < p
    · have hil : i < left.length := hip
      simp only [up, if_pos hip, Context.letterAt, hsw, hbw, List.getElem?_append_left hil]
    · have hpi : left.length ≤ i := Nat.le_of_not_gt hip
      have hpi' : left.length ≤ i + 1 := by omega
      have hsub : i + 1 - left.length = (i - left.length) + 1 := by omega
      simp only [up, if_neg hip, Context.letterAt, hsw, hbw,
        List.getElem?_append_right hpi', List.getElem?_append_right hpi,
        hsub, List.getElem?_cons_succ]
  exact hGo small.childPositions.length σ small p rfl hwf rfl rfl rfl rfl hlen hp hsp hbp hletter

end ErdosSzekeres
