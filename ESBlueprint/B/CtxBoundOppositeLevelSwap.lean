import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

set_option maxHeartbeats 4000000

/-- Swapping the first two occupied external levels and their sibling maxima preserves the context bound when the levels have opposite sides. This isolates the mixed-side residual comparison in the strip exchange: each side retains its own level order. No same-side level-swap invariance is asserted.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_bound_opposite_level_swap (σ : Ctx.Context) (hwf : σ.WellFormed)
  (hfirst : σ.extPositions 1 ≠ []) (hsecond : σ.extPositions 2 ≠ [])
  (hopposite : σ.sideAt 1 ≠ σ.sideAt 2) :
  ({ σ with
    word := σ.word.map (fun x ↦ match x with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext l s => Ctx.Letter.ext (if l = 1 then 2 else if l = 2 then 1 else l) s)
    maxima := [σ.maximumAt 2, σ.maximumAt 1] ++ σ.maxima.drop 2 } : Ctx.Context).bound = σ.bound := by
  classical
  let f (n l : ℕ) := if l = n then n + 1 else if l = n + 1 then n else l
  let tag (n : ℕ) : Ctx.Letter → Ctx.Letter := fun x ↦ match x with
    | .child => .child
    | .ext l s => .ext (f n l) s
  have hinv : ∀ n l, f n (f n l) = l := by
    intro n l
    dsimp [f]
    split_ifs <;> omega
  have hinj : ∀ n, Function.Injective (f n) := by
    intro n i j h
    simpa only [hinv] using congrArg (f n) h
  have hzero : ∀ n, 0 < n → f n 0 = 0 := by
    intro n hn
    simp [f, Nat.ne_of_lt hn]
  have hshift : ∀ n l, f (n + 1) (l + 1) = f n l + 1 := by
    intro n l
    dsimp [f]
    split_ifs <;> omega
  have hmemLevel : ∀ (c : Ctx.Context) l, l ∈ c.levels ↔ 1 ≤ l ∧ l ≤ c.maxima.length := by
    intro c l
    simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro h; exact ⟨l - 1, by omega, by omega⟩
  have hmem : ∀ (c : Ctx.Context) s top l, l ∈ c.levelsOn s top ↔
      1 ≤ l ∧ l ≤ c.maxima.length ∧ c.sideAt l = s ∧ (top = 0 ∨ l < top) := by
    intro c s top l
    simp [Ctx.Context.levelsOn, hmemLevel, and_assoc]
  have hsort : ∀ (c : Ctx.Context) s top, (c.levelsOn s top).Pairwise (· < ·) := by
    intro c s top
    apply List.Pairwise.filter
    exact List.pairwise_lt_range.map (fun i ↦ i + 1) (fun i j h ↦ by dsimp; omega)
  have horder : ∀ (c : Ctx.Context) n, c.sideAt n ≠ c.sideAt (n + 1) →
      ∀ i j, c.sideAt i = c.sideAt j → (f n i < f n j ↔ i < j) := by
    intro c n hop i j hs
    have hbad₁ : ¬ (i = n ∧ j = n + 1) := by rintro ⟨rfl, rfl⟩; exact hop hs
    have hbad₂ : ¬ (j = n ∧ i = n + 1) := by rintro ⟨rfl, rfl⟩; exact hop hs.symm
    dsimp [f]
    split_ifs <;> omega
  have hlevelMap : ∀ (c b : Ctx.Context) n, 0 < n → n + 1 ≤ c.maxima.length →
      b.maxima.length = c.maxima.length → c.sideAt n ≠ c.sideAt (n + 1) →
      (∀ l, b.sideAt (f n l) = c.sideAt l) →
      ∀ s top, (top = 0 ∨ c.sideAt top = s) →
        b.levelsOn s (f n top) = (c.levelsOn s top).map (f n) := by
    intro c b n hn hnm hlen hop hside s top htop
    have hbounds : ∀ l, (1 ≤ f n l ∧ f n l ≤ b.maxima.length) ↔
        (1 ≤ l ∧ l ≤ c.maxima.length) := by
      intro l
      rw [hlen]
      dsimp [f]
      split_ifs <;> omega
    have hpred : ∀ l, l ∈ c.levelsOn s top ↔ f n l ∈ b.levelsOn s (f n top) := by
      intro l
      rw [hmem, hmem, hside]
      have hb := hbounds l
      by_cases hs : c.sideAt l = s
      · rcases htop with ht | ht
        · simp only [ht, hzero n hn, true_or, and_true]
          tauto
        · have he := horder c n hop l top (hs.trans ht.symm)
          have hz : f n top = 0 ↔ top = 0 := by
            constructor
            · intro h; apply hinj n; simpa [hzero n hn] using h
            · intro h; simpa [h] using hzero n hn
          rw [hz, he]
          tauto
      · simp [hs]
    apply (hsort b s (f n top)).eq_of_mem_iff
    · apply List.pairwise_map.mpr
      apply (hsort c s top).imp_of_mem
      intro i j hi hj hij
      exact (horder c n hop i j (((hmem c s top i).mp hi).2.2.1.trans
        (((hmem c s top j).mp hj).2.2.1.symm))).mpr hij
    · intro l
      constructor
      · intro hl
        exact List.mem_map.mpr ⟨f n l, (hpred (f n l)).mpr (by simpa [hinv] using hl), hinv n l⟩
      · rintro hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
        exact (hpred i).mp hi
  have hgeometry : ∀ (c b : Ctx.Context) n,
      b.word.length = c.word.length → (∀ p, b.letterAt p = tag n (c.letterAt p)) →
      b.childPositions = c.childPositions ∧ b.numRuns = c.numRuns ∧
      (∀ l, b.extPositions (f n l) = c.extPositions l) ∧
      (∀ l, b.sideAt (f n l) = c.sideAt l) := by
    intro c b n hlen hletter
    have hc : ∀ p, b.letterAt p = .child ↔ c.letterAt p = .child := by
      intro p
      rw [hletter]
      cases c.letterAt p <;> simp [tag]
    have he : ∀ l, b.extPositions (f n l) = c.extPositions l := by
      intro l
      unfold Ctx.Context.extPositions
      rw [hlen]
      apply List.filter_congr
      intro p hp
      rw [hletter]
      cases h : c.letterAt p with
      | child => rfl
      | ext j s => simp [tag, (hinj n).eq_iff]
    refine ⟨?_, ?_, he, ?_⟩
    · simp only [Ctx.Context.childPositions, hlen, hc]
    · simp only [Ctx.Context.numRuns, hlen, ne_eq, hc]
    · intro l
      unfold Ctx.Context.sideAt
      rw [he]
      cases hh : (c.extPositions l).head? with
      | none => rfl
      | some p =>
        simp only
        rw [hletter]
        cases c.letterAt p <;> rfl
  have hbase : ∀ (c b : Ctx.Context) n, 0 < n → n + 1 ≤ c.maxima.length →
      b.a = c.a → b.u = c.u → b.k = c.k → b.maxima.length = c.maxima.length →
      b.word.length = c.word.length → (∀ p, b.letterAt p = tag n (c.letterAt p)) →
      (∀ l, 1 ≤ l → b.maximumAt (f n l) = c.maximumAt l) →
      c.sideAt n ≠ c.sideAt (n + 1) → b.base = c.base := by
    intro c b n hn hnm ha hu hk hm hw hl hmax hop
    obtain ⟨hc, hr, he, hs⟩ := hgeometry c b n hw hl
    have hls := hlevelMap c b n hn hnm hm hop hs
    have hfold : ∀ (ls : List ℕ) st,
        (ls.map (f n)).foldl (Ctx.Context.leftStep b) st =
          ls.foldl (Ctx.Context.leftStep c) st ∧
        (ls.map (f n)).foldl (Ctx.Context.rightStep b) st =
          ls.foldl (Ctx.Context.rightStep c) st := by
      intro ls
      induction ls with
      | nil => intro st; exact ⟨rfl, rfl⟩
      | cons l ls ih =>
        intro st
        have hL : Ctx.Context.leftStep b st (f n l) = Ctx.Context.leftStep c st l := by
          simp only [Ctx.Context.leftStep, he]
        have hR : Ctx.Context.rightStep b st (f n l) = Ctx.Context.rightStep c st l := by
          simp only [Ctx.Context.rightStep, he]
        simp only [List.map_cons, List.foldl_cons, hL, hR]
        exact ⟨(ih _).1, (ih _).2⟩
    have hext : ∀ s top, (top = 0 ∨ c.sideAt top = s) → ∀ p,
        b.leftExt s (f n top) p = c.leftExt s top p ∧
        b.rightExt s (f n top) p = c.rightExt s top p := by
      intro s top ht p
      constructor
      · rw [Ctx.Context.leftExt_eq, Ctx.Context.leftExt_eq, hls s top ht,
          List.sublists_map, List.map_map]
        congr 2
        apply List.map_congr_left
        intro ls hmem
        exact congrArg Prod.snd (hfold ls (p, 0)).1
      · rw [Ctx.Context.rightExt_eq, Ctx.Context.rightExt_eq, hls s top ht,
          List.sublists_map, List.map_map]
        congr 2
        apply List.map_congr_left
        intro ls hmem
        exact congrArg Prod.snd (hfold ls (p, 0)).2
    have hchain : ∀ s p q, b.chainExt s p q = c.chainExt s p q := by
      intro s p q
      have hp := (hext s 0 (Or.inl rfl) p).1
      have hq := (hext s 0 (Or.inl rfl) q).2
      rw [hzero n hn] at hp hq
      simp only [Ctx.Context.chainExt, hp, hq]
    have hjoin : ∀ s p q, b.joinExt s p q = c.joinExt s p q := by
      intro s p q
      unfold Ctx.Context.joinExt
      rw [hchain]
      have hzeroMap := hls s 0 (Or.inl rfl)
      rw [hzero n hn] at hzeroMap
      rw [hzeroMap, List.map_map]
      congr 3
      apply List.map_congr_left
      intro N hN
      have hmN := (hmem c s 0 N).mp hN
      dsimp only [Function.comp_def]
      rw [(hext s N (Or.inr hmN.2.2.1) p).1,
        (hext s N (Or.inr hmN.2.2.1) q).2, hmax N hmN.1]
    unfold Ctx.Context.base
    rw [hc]
    cases c.childPositions.head? with
    | none => rfl
    | some p => simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit, ha, hu, hk, hchain, hjoin]
  have hfuel : ∀ fuel (c b : Ctx.Context) n, 0 < n → n + 1 ≤ c.maxima.length →
      b.a = c.a → b.u = c.u → b.k = c.k → b.maxima.length = c.maxima.length →
      b.word.length = c.word.length → (∀ p, b.letterAt p = tag n (c.letterAt p)) →
      (∀ l, 1 ≤ l → b.maximumAt (f n l) = c.maximumAt l) →
      c.sideAt n ≠ c.sideAt (n + 1) →
      Ctx.Context.boundFuel fuel b = Ctx.Context.boundFuel fuel c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro c b n hn hnm ha hu hk hm hw hl hmax hop
      obtain ⟨hc, hr, he, hs⟩ := hgeometry c b n hw hl
      have hparts : ∀ B s m, Ctx.Context.boundFuel fuel (b.part B s m) =
          Ctx.Context.boundFuel fuel (c.part B s m) := by
        intro B s m
        apply ih (c.part B s m) (b.part B s m) (n + 1)
        · omega
        · simp only [Ctx.Context.part, List.length_cons]; omega
        · exact ha
        · exact hu
        · exact hk
        · simpa only [Ctx.Context.part, List.length_cons] using congrArg (· + 1) hm
        · simpa only [Ctx.Context.part_word_length] using hw
        · intro p
          by_cases hp : p < c.word.length
          · have hpb : p < b.word.length := by omega
            cases hpw : c.letterAt p with
            | child =>
              have hbw : b.letterAt p = .child := by simpa [hpw, tag] using hl p
              rw [Ctx.Context.part_letterAt_of_child b B s m hpb hbw,
                Ctx.Context.part_letterAt_of_child c B s m hp hpw]
              by_cases hkeep : p ∈ B
              · simp [hkeep, tag]
              · simp [hkeep, tag, f, show n ≠ 0 by omega]
            | ext l t =>
              have hbw : b.letterAt p = .ext (f n l) t := by simpa [hpw, tag] using hl p
              rw [Ctx.Context.part_letterAt_of_ext b B s m hpb hbw,
                Ctx.Context.part_letterAt_of_ext c B s m hp hpw]
              simp [tag, hshift]
          · have hpb : ¬ p < b.word.length := by omega
            have hbNone : (b.part B s m).word[p]? = none :=
              List.getElem?_eq_none (by
                simpa only [Ctx.Context.part_word_length] using (Nat.le_of_not_gt hpb))
            have hcNone : (c.part B s m).word[p]? = none :=
              List.getElem?_eq_none (by
                simpa only [Ctx.Context.part_word_length] using (Nat.le_of_not_gt hp))
            simp [Ctx.Context.letterAt, hbNone, hcNone, tag]
        · intro l hlpos
          by_cases hl1 : l = 1
          · subst l
            simp [f, show n ≠ 0 by omega, Ctx.Context.maximumAt, Ctx.Context.part]
          · obtain ⟨q, rfl⟩ : ∃ q, l = q + 1 := ⟨l - 1, by omega⟩
            have hq : 1 ≤ q := by omega
            have hfn : 1 ≤ f n q := by dsimp [f]; split_ifs <;> omega
            rw [hshift]
            change (m :: b.maxima)[f n q]?.getD 0 = (m :: c.maxima)[q]?.getD 0
            have hget : ∀ (A : List ℕ) r, 1 ≤ r →
                (m :: A)[r]?.getD 0 = A[r - 1]?.getD 0 := by
              intro A r hr
              cases r with
              | zero => omega
              | succ r => simp
            rw [hget b.maxima (f n q) hfn, hget c.maxima q hq]
            exact hmax q hq
        · rw [Ctx.Context.part_sideAt_succ c B s m (by omega),
            Ctx.Context.part_sideAt_succ c B s m (by omega)]
          exact hop
      rw [Ctx.Context.boundFuel.eq_2, Ctx.Context.boundFuel.eq_2, hr]
      by_cases hrun : c.numRuns ≤ 1
      · simp only [if_pos hrun]
        exact hbase c b n hn hnm ha hu hk hm hw hl hmax hop
      · simp only [if_neg hrun]
        have hblocks : b.blocks = c.blocks := by simp only [Ctx.Context.blocks, hc]
        rw [hblocks, hc, hk]
        congr 2
        apply List.flatMap_congr
        intro B hB
        apply List.flatMap_congr
        intro d hd
        rw [hparts, hparts, hparts, hparts]
  let b : Ctx.Context := { σ with
    word := σ.word.map (tag 1)
    maxima := [σ.maximumAt 2, σ.maximumAt 1] ++ σ.maxima.drop 2 }
  have hlen : 2 ≤ σ.maxima.length := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hsecond
    have hp' := (List.mem_filter.mp hp).2
    cases he : σ.letterAt p with
    | child => simp [he] at hp'
    | ext l s =>
      have hl : l = 2 := by simpa [he] using hp'
      subst l
      exact (hwf.2.2.2.2.2 p 2 s he).2.1
  have hbLen : b.maxima.length = σ.maxima.length := by simp [b]; omega
  have hbWord : b.word.length = σ.word.length := by simp [b]
  have hbLetter : ∀ p, b.letterAt p = tag 1 (σ.letterAt p) := by
    intro p
    simp only [Ctx.Context.letterAt, b, List.getElem?_map]
    cases σ.word[p]? <;> rfl
  have hbMax : ∀ l, 1 ≤ l → b.maximumAt (f 1 l) = σ.maximumAt l := by
    intro l hl
    rcases hm : σ.maxima with _ | ⟨x, rest⟩
    · simp [hm] at hlen
    rcases rest with _ | ⟨y, tail⟩
    · simp [hm] at hlen
    by_cases h1 : l = 1
    · subst l; simp [b, f, Ctx.Context.maximumAt, hm]
    by_cases h2 : l = 2
    · subst l; simp [b, f, Ctx.Context.maximumAt, hm]
    obtain ⟨q, rfl⟩ : ∃ q, l = q + 3 := ⟨l - 3, by omega⟩
    simp [b, f, Ctx.Context.maximumAt, hm, show q + 3 ≠ 1 by omega,
      show q + 3 ≠ 2 by omega]
  have hc := (hgeometry σ b 1 hbWord hbLetter).1
  change b.bound = σ.bound
  unfold Ctx.Context.bound
  rw [hc]
  exact hfuel _ σ b 1 (by omega) hlen rfl rfl rfl hbLen hbWord hbLetter hbMax hopposite

end ErdosSzekeres
