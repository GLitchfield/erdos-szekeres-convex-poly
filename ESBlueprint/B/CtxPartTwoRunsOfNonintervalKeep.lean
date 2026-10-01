import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A nonempty proper canonical keep set that is not a child-order interval block forces its recursive part to have at least two physical child runs. A single physical run would give a numeric interval of retained positions; filtering all word positions by source children preserves its infix and therefore exhibits a proper child-order block. The context, keep list, side, and new maximum are arbitrary; no well-formedness or positive-level assumption is needed. Supplies the run-structure bridge for the interleaved k=3 boundary of maximal-segment exchange.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_two_runs_of_noninterval_keep (σ : Ctx.Context) (keep : List ℕ)
  (hnonempty : σ.childPositions.filter (fun p ↦ p ∈ keep) ≠ [])
  (hproper : (σ.childPositions.filter (fun p ↦ p ∈ keep)).length < σ.childPositions.length)
  (hnoninterval : σ.childPositions.filter (fun p ↦ p ∈ keep) ∉ σ.blocks)
  (s : Ctx.Side) (m : ℕ) :
  2 ≤ (σ.part keep s m).numRuns := by
  classical
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
  by_contra h
  let τ := σ.part keep s m
  have hruns1 : τ.numRuns ≤ 1 := by
    change ¬ 2 ≤ τ.numRuns at h
    omega
  have hcanonical : τ.childPositions = σ.childPositions.filter (fun p ↦ p ∈ keep) :=
    Ctx.Context.part_childPositions σ keep s m
  have hτne : τ.childPositions ≠ [] := by simpa only [hcanonical] using hnonempty
  have hproperτ : τ.childPositions.length < σ.childPositions.length := by
    simpa only [hcanonical] using hproper
  obtain ⟨b, hrange⟩ := hInterval τ hruns1 hτne
  let n := τ.childPositions.length
  have hnpos : 0 < n := by
    dsimp only [n]
    cases he : τ.childPositions with
    | nil => exact (hτne he).elim
    | cons p ps => simp
  have hRange : τ.childPositions = List.range' b n := hrange
  have hbound : b + n ≤ σ.word.length := by
    have hpτ : b + n - 1 ∈ τ.childPositions := by
      rw [hRange]
      exact List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have hpσ : b + n - 1 ∈ σ.childPositions := by
      rw [hcanonical] at hpτ
      exact (List.mem_filter.mp hpτ).1
    have hpbound := List.mem_range.mp (List.mem_filter.mp hpσ).1
    omega
  let after := List.range' (b + n) (σ.word.length - (b + n))
  have hfront : List.range' 0 b ++ List.range' b n = List.range' 0 (b + n) := by
    simpa only [Nat.zero_add] using
      (List.range'_append_1 (s := 0) (m := b) (n := n))
  have htotal : b + n + (σ.word.length - (b + n)) = σ.word.length := by omega
  have hrear : List.range' 0 (b + n) ++ after = List.range' 0 σ.word.length := by
    simpa only [after, Nat.zero_add, htotal] using
      (List.range'_append_1 (s := 0) (m := b + n) (n := σ.word.length - (b + n)))
  have hwhole : List.range' 0 b ++ List.range' b n ++ after = List.range σ.word.length := by
    rw [hfront]
    simpa only [List.range_eq_range'] using hrear
  have hRangeInfix : (List.range' b n).IsInfix (List.range σ.word.length) :=
    ⟨List.range' 0 b, after, hwhole⟩
  have hFilter : (List.range' b n).filter (fun p => decide (σ.letterAt p = Ctx.Letter.child)) =
      List.range' b n := by
    apply List.filter_eq_self.mpr
    intro p hp
    have hpτ : p ∈ τ.childPositions := by rw [hRange]; exact hp
    have hpσ : p ∈ σ.childPositions := by
      rw [hcanonical] at hpτ
      exact (List.mem_filter.mp hpτ).1
    exact (List.mem_filter.mp hpσ).2
  have hInfix : τ.childPositions.IsInfix σ.childPositions := by
    have hh := hRangeInfix.filter (fun p => decide (σ.letterAt p = Ctx.Letter.child))
    rw [hFilter] at hh
    change (List.range' b n).IsInfix σ.childPositions at hh
    rw [← hRange] at hh
    exact hh
  obtain ⟨pref, suff, hdecomp⟩ := hInfix
  have hσeq : σ.childPositions = pref ++ τ.childPositions ++ suff := hdecomp.symm
  have hlength : σ.childPositions.length = pref.length + n + suff.length := by
    simpa only [List.length_append, n] using congrArg List.length hσeq
  have hn1 : n - 1 + 1 = n := by omega
  have hdrop : (σ.childPositions.drop pref.length).take n = τ.childPositions := by
    simp only [hσeq, List.append_assoc, List.drop_left, List.take_left, n]
  apply hnoninterval
  rw [← hcanonical]
  unfold Ctx.Context.blocks
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hproperτ⟩
  apply List.mem_flatMap.mpr
  refine ⟨pref.length, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_map.mpr
  refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
  simpa only [hn1] using hdrop

end ErdosSzekeres
