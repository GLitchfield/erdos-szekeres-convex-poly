import ESBlueprint.B.CtxBoundOppositeLevelSwap

namespace ErdosSzekeres

/-- Removing two nonempty disjoint child blocks on opposite sides commutes at the level of the final residual context bound. No interval or endpoint assumption is needed. The proof identifies the two residual words by swapping their first two external levels and applies the checked opposite-side level-swap theorem. This supplies exact residual transport for mixed-side strip exchanges.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_bound_opposite_removals_commute (σ : Ctx.Context) (hwf : σ.WellFormed) (A B : List ℕ)
  (hA : ∀ p ∈ A, p ∈ σ.childPositions) (hB : ∀ p ∈ B, p ∈ σ.childPositions)
  (hAne : A ≠ []) (hBne : B ≠ []) (hdisjoint : ∀ p ∈ A, p ∉ B)
  (s t : Ctx.Side) (hopposite : s ≠ t) (m n : ℕ)
  (hm1 : 1 ≤ m) (hmk : m ≤ σ.k - 2) (hn1 : 1 ≤ n) (hnk : n ≤ σ.k - 2) :
  let keep := σ.childPositions.filter (fun p ↦ p ∉ A ∧ p ∉ B)
  ((σ.part (σ.childPositions.filter (· ∉ A)) s m).part keep t n).bound =
    ((σ.part (σ.childPositions.filter (· ∉ B)) t n).part keep s m).bound := by
  let keep := σ.childPositions.filter (fun p ↦ p ∉ A ∧ p ∉ B)
  let RA := σ.childPositions.filter (· ∉ A)
  let RB := σ.childPositions.filter (· ∉ B)
  let α := σ.part RA s m
  let β := σ.part RB t n
  let x := α.part keep t n
  let y := β.part keep s m
  let tag : Ctx.Letter → Ctx.Letter := fun z ↦ match z with
    | .child => .child
    | .ext l u => .ext (if l = 1 then 2 else if l = 2 then 1 else l) u
  have hread (c : Ctx.Context) (K : List ℕ) (u : Ctx.Side) (v p : ℕ)
      (hp : p < c.word.length) :
      (c.part K u v).letterAt p = match c.letterAt p with
        | .child => if p ∈ K then .child else .ext 1 u
        | .ext l r => .ext (l + 1) r := by
    cases h : c.letterAt p with
    | child => exact Ctx.Context.part_letterAt_of_child c K u v hp h
    | ext l r => exact Ctx.Context.part_letterAt_of_ext c K u v hp h
  have hread₂ (K L : List ℕ) (u v : Ctx.Side) (a b p : ℕ) (hp : p < σ.word.length) :
      ((σ.part K u a).part L v b).letterAt p = match σ.letterAt p with
        | .child => if p ∈ K then (if p ∈ L then .child else .ext 1 v) else .ext 2 u
        | .ext l r => .ext (l + 1 + 1) r := by
    rw [hread _ _ _ _ _ (by simpa only [Ctx.Context.part_word_length] using hp),
      hread σ K u a p hp]
    cases h : σ.letterAt p with
    | child => by_cases hK : p ∈ K <;> simp [hK]
    | ext l r => rfl
  have hαwf : α.WellFormed := hwf.part RA s hm1 hmk
  have hxwf : x.WellFormed := hαwf.part keep t hn1 hnk
  have hlenx : x.word.length = σ.word.length := by simp [x, α, Ctx.Context.part_word_length]
  have hleny : y.word.length = σ.word.length := by simp [y, β, Ctx.Context.part_word_length]
  have hletters (p : ℕ) (hp : p < σ.word.length) : tag (x.letterAt p) = y.letterAt p := by
    change tag (((σ.part RA s m).part keep t n).letterAt p) =
      ((σ.part RB t n).part keep s m).letterAt p
    rw [hread₂ _ _ _ _ _ _ _ hp, hread₂ _ _ _ _ _ _ _ hp]
    cases hc : σ.letterAt p with
    | child =>
      have hcp : p ∈ σ.childPositions := by
        simp [Ctx.Context.childPositions, hp, hc]
      by_cases ha : p ∈ A
      · have hb : p ∉ B := hdisjoint p ha
        simp [RA, RB, keep, hcp, ha, hb, tag]
      · by_cases hb : p ∈ B <;> simp [RA, RB, keep, hcp, ha, hb, tag]
    | ext l u =>
      have hl := (hwf.2.2.2.2.2 p l u hc).1
      simp [tag, show l + 1 + 1 ≠ 1 by omega, show l + 1 + 1 ≠ 2 by omega]
  have hword : x.word.map tag = y.word := by
    apply List.ext_getElem (by simpa using hlenx.trans hleny.symm)
    intro p hp hpy
    have hpx : p < x.word.length := by simpa using hp
    have hpσ : p < σ.word.length := by omega
    simpa only [List.getElem_map, Ctx.Context.letterAt, List.getElem?_eq_getElem hpx,
      List.getElem?_eq_getElem hpy, Option.getD_some] using hletters p hpσ
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil A hAne
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hBne
  have haCP := hA a ha
  have hbCP := hB b hb
  have haB := hdisjoint a ha
  have hbA : b ∉ A := fun hb' => hdisjoint b hb' hb
  have hap : a < σ.word.length ∧ σ.letterAt a = .child := by
    simpa only [Ctx.Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq] using haCP
  have hbp : b < σ.word.length ∧ σ.letterAt b = .child := by
    simpa only [Ctx.Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq] using hbCP
  have hax : x.letterAt a = .ext 2 s := by
    change ((σ.part RA s m).part keep t n).letterAt a = _
    rw [hread₂ _ _ _ _ _ _ _ hap.1]
    simp [hap.2, RA, ha]
  have hbx : x.letterAt b = .ext 1 t := by
    change ((σ.part RA s m).part keep t n).letterAt b = _
    rw [hread₂ _ _ _ _ _ _ _ hbp.1]
    simp [hbp.2, RA, keep, hbCP, hbA, hb]
  have haExt : a ∈ x.extPositions 2 := by
    simp [Ctx.Context.extPositions, hlenx, hap.1, hax]
  have hbExt : b ∈ x.extPositions 1 := by
    simp [Ctx.Context.extPositions, hlenx, hbp.1, hbx]
  have hxfirst : x.extPositions 1 ≠ [] := by intro h; simpa [h] using hbExt
  have hxsecond : x.extPositions 2 ≠ [] := by intro h; simpa [h] using haExt
  have hxs : s = x.sideAt 2 := (hxwf.2.2.2.2.2 a 2 s hax).2.2
  have hxt : t = x.sideAt 1 := (hxwf.2.2.2.2.2 b 1 t hbx).2.2
  have hxop : x.sideAt 1 ≠ x.sideAt 2 := by rw [← hxs, ← hxt]; exact Ne.symm hopposite
  have hswap := ctx_bound_opposite_level_swap x hxwf hxfirst hxsecond hxop
  have hctx : ({ x with
      word := x.word.map tag
      maxima := [x.maximumAt 2, x.maximumAt 1] ++ x.maxima.drop 2 } : Ctx.Context) = y := by
    have hmax : [x.maximumAt 2, x.maximumAt 1] ++ x.maxima.drop 2 = y.maxima := by
      simp [x, α, y, β, Ctx.Context.maximumAt, Ctx.Context.part_maxima]
    change Ctx.Context.mk σ.a σ.u σ.k (x.word.map tag)
      ([x.maximumAt 2, x.maximumAt 1] ++ x.maxima.drop 2) =
      Ctx.Context.mk σ.a σ.u σ.k y.word y.maxima
    rw [hword, hmax]
  change x.bound = y.bound
  change ({ x with
      word := x.word.map tag
      maxima := [x.maximumAt 2, x.maximumAt 1] ++ x.maxima.drop 2 } : Ctx.Context).bound = x.bound at hswap
  rw [hctx] at hswap
  exact hswap.symm

end ErdosSzekeres
