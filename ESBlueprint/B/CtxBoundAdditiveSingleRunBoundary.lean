import ESBlueprint.B.CtxBoundAdditivePrefixSuffix

namespace ErdosSzekeres

/-- Boundary additivity in the original single-run context API: a nonempty child set with at most one run is a contiguous interval, so every proper prefix or suffix partition is covered by ctx_bound_additive_prefix_suffix.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_additive_prefix_suffix
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_single_run_boundary (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (hboundary : keep <+: σ.childPositions ∨ keep <:+ σ.childPositions) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  have hchildNe : σ.childPositions ≠ [] := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil keep hne
    exact List.ne_nil_of_mem (hkeep p hp)
  obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
  have hb : b ∈ σ.childPositions := by
    rw [hcons]
    exact List.mem_cons_self
  have hordered : σ.childPositions.Pairwise (· ≤ ·) :=
    (Ctx.Context.childPositions_pairwise σ).imp le_of_lt
  have hmin : ∀ p ∈ σ.childPositions, b ≤ p := by
    intro p hp
    have h := hordered.rel_head hp
    simpa [hcons] using h
  let starts := (List.range σ.word.length).filter fun p ↦
    σ.letterAt p = Ctx.Letter.child ∧
      (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
  have hstartsLen : starts.length ≤ 1 := by
    simpa [starts, Ctx.Context.numRuns] using hruns
  have hstartsNodup : starts.Nodup := by
    exact List.nodup_range.filter _
  have hbRange : b < σ.word.length := by
    exact List.mem_range.1 (List.mem_filter.1 hb).1
  have hbLetter : σ.letterAt b = Ctx.Letter.child :=
    of_decide_eq_true (List.mem_filter.1 hb).2
  have hbStartCondition :
      b = 0 ∨ σ.letterAt (b - 1) ≠ Ctx.Letter.child := by
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      intro hprev
      have hprevMem : b - 1 ∈ σ.childPositions := by
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
  have hpred : ∀ p ∈ σ.childPositions, p ≠ b → p - 1 ∈ σ.childPositions := by
    intro p hp hpb
    have hpRange : p < σ.word.length :=
      List.mem_range.1 (List.mem_filter.1 hp).1
    have hpLetter : σ.letterAt p = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hp).2
    have hpPositive : 0 < p := by
      have := hmin p hp
      omega
    by_contra hprevMem
    have hprevLetter : σ.letterAt (p - 1) ≠ Ctx.Letter.child := by
      intro hletter
      apply hprevMem
      apply List.mem_filter.2
      exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
    have hpStart : p ∈ starts := by
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
    exact hpb (hstartUnique p hpStart)
  have hfill : ∀ p ∈ σ.childPositions, ∀ q, b ≤ q → q ≤ p →
      q ∈ σ.childPositions := by
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
  let e := σ.childPositions.getLast hchildNe
  have he : e ∈ σ.childPositions := by
    dsimp [e]
    exact List.getLast_mem _
  have hmax : ∀ p ∈ σ.childPositions, p ≤ e := by
    intro p hp
    simpa [e] using hordered.rel_getLast hp
  have hbe : b ≤ e := hmin e he
  have hmemRange : ∀ p, p ∈ σ.childPositions ↔
      p ∈ List.range' b (e + 1 - b) := by
    intro p
    simp only [List.mem_range'_1]
    constructor
    · intro hp
      exact ⟨hmin p hp, by have := hmax p hp; omega⟩
    · rintro ⟨hbp, hp⟩
      exact hfill e he p hbp (by omega)
  have hperm : σ.childPositions.Perm (List.range' b (e + 1 - b)) :=
    (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup σ)
      List.nodup_range').2 hmemRange
  have hrange : σ.childPositions = List.range' b (e + 1 - b) :=
    List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
  have hlen : σ.childPositions.length = e + 1 - b := by
    rw [hrange]
    simp
  have hinterval : σ.childPositions = List.range' b σ.childPositions.length := by
    rw [hlen]
    exact hrange
  have hcomplement : ∀ l r : ℕ, σ.childPositions = List.range' b (l + r) →
      (σ.childPositions.filter (fun p ↦ p ∉ List.range' b l) =
          List.range' (b + l) r) ∧
      (σ.childPositions.filter (fun p ↦ p ∉ List.range' (b + l) r) =
          List.range' b l) := by
    intro l r hpos
    constructor
    · rw [hpos, ← List.range'_append_1, List.filter_append]
      have hnil : (List.range' b l).filter (fun p ↦ p ∉ List.range' b l) = [] := by
        apply List.filter_eq_nil_iff.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      have hself : (List.range' (b + l) r).filter
          (fun p ↦ p ∉ List.range' b l) = List.range' (b + l) r := by
        apply List.filter_eq_self.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      rw [hnil, hself, List.nil_append]
    · rw [hpos, ← List.range'_append_1, List.filter_append]
      have hself : (List.range' b l).filter
          (fun p ↦ p ∉ List.range' (b + l) r) = List.range' b l := by
        apply List.filter_eq_self.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      have hnil : (List.range' (b + l) r).filter
          (fun p ↦ p ∉ List.range' (b + l) r) = [] := by
        apply List.filter_eq_nil_iff.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      rw [hself, hnil, List.append_nil]
  rcases hboundary with hprefix | hsuffix
  · let n := σ.childPositions.length
    let l := keep.length
    let r := n - l
    have hl : 0 < l := by
      simpa [l] using List.length_pos_iff.2 hne
    have hr : 0 < r := by
      dsimp [r, n, l]
      omega
    have hsum : l + r = n := by
      dsimp [r, n, l]
      omega
    have hpos : σ.childPositions = List.range' b (l + r) := by
      rw [hsum]
      simpa [n] using hinterval
    have hkeepRange : keep = List.range' b l := by
      calc
        keep = σ.childPositions.take keep.length := List.prefix_iff_eq_take.mp hprefix
        _ = (List.range' b (l + r)).take l := by rw [hpos]
        _ = List.range' b l := List.take_range'_of_length_ge (by omega)
    have hrest : σ.childPositions.filter (fun p ↦ p ∉ keep) =
        List.range' (b + l) r := by
      rw [hkeepRange]
      exact (hcomplement l r hpos).1
    rw [hrest, hkeepRange]
    exact ctx_bound_additive_prefix_suffix σ hwf b l r hpos hl hr d hd hdk
  · let n := σ.childPositions.length
    let r := keep.length
    let l := n - r
    have hr : 0 < r := by
      simpa [r] using List.length_pos_iff.2 hne
    have hl : 0 < l := by
      dsimp [l, n, r]
      omega
    have hsum : l + r = n := by
      dsimp [l, n, r]
      omega
    have hpos : σ.childPositions = List.range' b (l + r) := by
      rw [hsum]
      simpa [n] using hinterval
    have hkeepRange : keep = List.range' (b + l) r := by
      calc
        keep = σ.childPositions.drop
            (σ.childPositions.length - keep.length) :=
          List.suffix_iff_eq_drop.mp hsuffix
        _ = (List.range' b (l + r)).drop l := by
          rw [hpos]
          simp only [List.length_range']
          congr 1
          dsimp [l, r, n]
          omega
        _ = List.range' (b + l) r := by
          simp only [List.drop_range', Nat.mul_one]
          congr 1
          omega
    have hrest : σ.childPositions.filter (fun p ↦ p ∉ keep) =
        List.range' b l := by
      rw [hkeepRange]
      exact (hcomplement l r hpos).2
    obtain ⟨hleft, hright⟩ :=
      ctx_bound_additive_prefix_suffix σ hwf b l r hpos hl hr d hd hdk
    rw [hrest, hkeepRange]
    constructor
    · simpa only [Nat.add_comm] using hright
    · simpa only [Nat.add_comm] using hleft

end ErdosSzekeres
