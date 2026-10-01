import ESBlueprint.B.CtxPositiveBoundAttainedByIntervalCut
import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

/-- A positive raw context bound with opposite global axis at most two has a positive single-run descendant on a path choosing only the other axis. The witness preserves globals and positions, prepends legal maxima, shifts old external levels and indexed sides, and records removed original children as chosen-side new levels. Positive actual external labels suffice for arbitrary history and physical length; finite child-count descent exposes the marker-order cost needed for axis-two ROOT-NF.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_positive_bound_has_same_axis_single_run_leaf (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2)
    (hbound : 0 < σ.bound) :
    ∃ (τ : Ctx.Context) (history : List ℕ),
      τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧
      τ.word.length = σ.word.length ∧ τ.maxima = history ++ σ.maxima ∧
      (∀ c ∈ history, 1 ≤ c ∧ c ≤ σ.k - 2) ∧
      τ.numRuns ≤ 1 ∧ 0 < τ.base ∧
      (∀ p ∈ τ.childPositions, p ∈ σ.childPositions) ∧
      (∀ p, p < σ.word.length →
        match σ.letterAt p with
        | Ctx.Letter.child =>
          τ.letterAt p = Ctx.Letter.child ∨
            ∃ j, 1 ≤ j ∧ j ≤ history.length ∧ τ.letterAt p = Ctx.Letter.ext j s
        | Ctx.Letter.ext j v => τ.letterAt p = Ctx.Letter.ext (j + history.length) v) ∧
      (∀ j, 1 ≤ j → τ.sideAt (j + history.length) = σ.sideAt j) ∧
      (∀ j, 1 ≤ j → j ≤ history.length → τ.sideAt j = s) := by
  classical
  -- Reuse the accepted R18 raw proper-part-zero proof locally on this main-based branch.
  have hUnitZero (σ : Ctx.Context)
    (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
    (s : Ctx.Side)
    (hunit : match s with | Ctx.Side.lower => σ.u ≤ 2 | Ctx.Side.upper => σ.a ≤ 2)
    (keep : List ℕ) (m r : ℕ)
    (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
    (∀ p ∈ (σ.part keep s m).childPositions,
      (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0) ∧
      (σ.part keep s m).bound = 0 := by
    classical
    let τ := σ.part keep s m
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [Ctx.Context.part_extPositions_one hpositive keep s m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hside : τ.sideAt 1 = s :=
      Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
    have hone : 1 ∈ τ.levelsOn s 0 := by
      apply List.mem_filter.mpr
      refine ⟨?_, by simp [hside]⟩
      change 1 ∈ (σ.part keep s m).levels
      rw [Ctx.Context.part_levels]
      exact List.mem_cons_self
    have hsub : [1].Sublist (τ.levelsOn s 0) := List.singleton_sublist.mpr hone
    have hzero : ∀ p ∈ τ.childPositions,
        (match s with
        | Ctx.Side.lower => τ.cupLimit p p
        | Ctx.Side.upper => τ.capLimit p p) = 0 := by
      intro p hp
      have hpkeep : p ∈ keep := by
        rw [Ctx.Context.part_childPositions] at hp
        simpa using (List.mem_filter.mp hp).2
      have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
      have hExt : 1 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p := by
        by_cases hrp : r < p
        · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
            intro hn
            have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
              List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
            rw [hn] at hm
            cases hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (τ.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
            (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
          change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤ τ.leftExt s 0 p at hv
          simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
            List.getLast?_eq_some_getLast hnon] at hv
          omega
        · have hpr : p < r := by omega
          have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
            intro hn
            have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
              List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
            rw [hn] at hm
            cases hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (τ.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
            (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
          change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤ τ.rightExt s 0 p at hv
          simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
            List.head?_eq_some_head hnon] at hv
          omega
      have hchain : 1 ≤ τ.chainExt s p p := hExt
      cases s with
      | lower =>
        change σ.u ≤ 2 at hunit
        change min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower p p) = 0
        omega
      | upper =>
        change σ.a ≤ 2 at hunit
        change min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper p p) = 0
        omega
    have hz : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0 := by
      intro p hp
      have h := hzero p hp
      cases s with
      | lower => exact Or.inl h
      | upper => exact Or.inr h
    have hsum : (τ.childPositions.map
        (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp only [Ctx.Context.baseOf, if_pos (hz p hp)]
    exact ⟨hzero, Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hsum)⟩
  let Witness (ρ : Ctx.Context) : Prop :=
    ∃ (τ : Ctx.Context) (history : List ℕ),
      τ.a = ρ.a ∧ τ.u = ρ.u ∧ τ.k = ρ.k ∧
      τ.word.length = ρ.word.length ∧ τ.maxima = history ++ ρ.maxima ∧
      (∀ c ∈ history, 1 ≤ c ∧ c ≤ ρ.k - 2) ∧
      τ.numRuns ≤ 1 ∧ 0 < τ.base ∧
      (∀ p ∈ τ.childPositions, p ∈ ρ.childPositions) ∧
      (∀ p, p < ρ.word.length →
        match ρ.letterAt p with
        | Ctx.Letter.child =>
          τ.letterAt p = Ctx.Letter.child ∨
            ∃ j, 1 ≤ j ∧ j ≤ history.length ∧ τ.letterAt p = Ctx.Letter.ext j s
        | Ctx.Letter.ext j v => τ.letterAt p = Ctx.Letter.ext (j + history.length) v) ∧
      (∀ j, 1 ≤ j → τ.sideAt (j + history.length) = ρ.sideAt j) ∧
      (∀ j, 1 ≤ j → j ≤ history.length → τ.sideAt j = s)
  change Witness σ
  have hPositivePart (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side) (m : ℕ) :
      ∀ p j u, (ρ.part keep v m).letterAt p = Ctx.Letter.ext j u → 1 ≤ j := by
    intro p j u hx
    have hp : p < ρ.word.length := by
      by_contra h
      rw [Ctx.Context.letterAt_of_length_le (ρ.part keep v m)
        (by rw [Ctx.Context.part_word_length]; omega)] at hx
      cases hx
    cases he : ρ.letterAt p with
    | child =>
      rw [Ctx.Context.part_letterAt_of_child ρ keep v m hp he] at hx
      split at hx
      · cases hx
      · cases hx; omega
    | ext l w =>
      rw [Ctx.Context.part_letterAt_of_ext ρ keep v m hp he] at hx
      cases hx
      omega
  have hRemoved (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side) (m : ℕ)
      (hsmall : (ρ.part keep v m).childPositions.length < ρ.childPositions.length) :
      ∃ r ∈ ρ.childPositions, r ∉ keep := by
    by_contra hn
    push_neg at hn
    have he : ρ.childPositions.filter (fun p => p ∈ keep) = ρ.childPositions := by
      apply List.filter_eq_self.mpr
      intro p hp
      simpa using hn p hp
    rw [Ctx.Context.part_childPositions, he] at hsmall
    omega
  have hmain : ∀ n : ℕ, ∀ (ρ : Ctx.Context), ρ.childPositions.length = n →
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) t ≤ 2 →
      0 < ρ.bound → Witness ρ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ρ hcount hPos hUnit hBound
      by_cases hruns : ρ.numRuns ≤ 1
      · have hbase : 0 < ρ.base := by
          simpa only [Ctx.Context.bound, Ctx.Context.boundFuel.eq_2, if_pos hruns] using hBound
        refine ⟨ρ, [], rfl, rfl, rfl, rfl, rfl, ?_, hruns, hbase, ?_, ?_, ?_, ?_⟩
        · simp
        · intro p hp; exact hp
        · intro p hp
          cases he : ρ.letterAt p with
          | child => exact Or.inl rfl
          | ext j v => simpa using he
        · intro j hj; simp
        · intro j hj hle; simp at hle; omega
      have hruns2 : 2 ≤ ρ.numRuns := by omega
      have hRecurse (keep : List ℕ) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ ρ.k - 2)
          (hSmall : (ρ.part keep s m).childPositions.length < ρ.childPositions.length)
          (hPart : 0 < (ρ.part keep s m).bound) : Witness ρ := by
        let A := ρ.part keep s m
        have hAcount : A.childPositions.length < n := by simpa only [hcount] using hSmall
        have hAunit : (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) t ≤ 2 := hUnit
        obtain ⟨τ, history, ha, hu, hk, hlen, hmax, hlegal,
          hrun, hbase, hchildren, hword, hold, hnew⟩ :=
          ih A.childPositions.length hAcount A rfl (hPositivePart ρ keep s m) hAunit hPart
        obtain ⟨r, hr, hnot⟩ := hRemoved ρ keep s m hSmall
        have hrnew : r ∈ A.extPositions 1 := by
          rw [Ctx.Context.part_extPositions_one hPos keep s m]
          exact List.mem_filter.mpr ⟨hr, by simpa using hnot⟩
        have hAnew : A.sideAt 1 = s := Ctx.Context.part_sideAt_one_of_mem hPos keep s m hrnew
        have hprefix : (history ++ [m]).length = history.length + 1 := by simp
        refine ⟨τ, history ++ [m], ha, hu, hk, ?_, ?_, ?_, hrun, hbase, ?_, ?_, ?_, ?_⟩
        · exact hlen.trans (Ctx.Context.part_word_length ρ keep s m)
        · simpa only [A, Ctx.Context.part, List.append_assoc, List.cons_append,
            List.nil_append] using hmax
        · intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · simpa only [A, Ctx.Context.part] using hlegal c hc
          · have hc' : c = m := by simpa using hc
            subst c
            exact ⟨hm, hmk⟩
        · intro p hp
          have hpA := hchildren p hp
          rw [Ctx.Context.part_childPositions] at hpA
          exact (List.mem_filter.mp hpA).1
        · intro p hp
          have hpA : p < A.word.length := by rw [Ctx.Context.part_word_length]; exact hp
          cases he : ρ.letterAt p with
          | child =>
            by_cases hkeep : p ∈ keep
            · have heA : A.letterAt p = Ctx.Letter.child := by
                rw [Ctx.Context.part_letterAt_of_child ρ keep s m hp he, if_pos hkeep]
              have hw := hword p hpA
              rw [heA] at hw
              rcases hw with hc | ⟨j, hj, hjlen, heτ⟩
              · exact Or.inl hc
              · exact Or.inr ⟨j, hj, by rw [hprefix]; omega, heτ⟩
            · have heA : A.letterAt p = Ctx.Letter.ext 1 s := by
                rw [Ctx.Context.part_letterAt_of_child ρ keep s m hp he, if_neg hkeep]
              have hw := hword p hpA
              rw [heA] at hw
              exact Or.inr ⟨history.length + 1, by omega, by rw [hprefix],
                by simpa only [Nat.add_comm] using hw⟩
          | ext j v =>
            have heA : A.letterAt p = Ctx.Letter.ext (j + 1) v :=
              Ctx.Context.part_letterAt_of_ext ρ keep s m hp he
            have hw := hword p hpA
            rw [heA] at hw
            simpa only [hprefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw
        · intro j hj
          have ho := hold (j + 1) (by omega)
          rw [Ctx.Context.part_sideAt_succ ρ keep s m hj] at ho
          simpa only [hprefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho
        · intro j hj hle
          rw [hprefix] at hle
          by_cases hjp : j ≤ history.length
          · exact hnew j hj hjp
          · have hj' : j = 1 + history.length := by omega
            rw [hj']
            exact (hold 1 (by omega)).trans hAnew
      obtain ⟨block, hb, d, hd, hdk, hatt⟩ :=
        ctx_positive_bound_attained_by_interval_cut ρ hruns2 hBound
      let rest := ρ.childPositions.filter (fun p => p ∉ block)
      have hBsmall (v : Ctx.Side) (m : ℕ) :
          (ρ.part block v m).childPositions.length < ρ.childPositions.length :=
        Ctx.Context.part_childPositions_length_lt_of_mem_blocks hb v m
      have hRsmall (v : Ctx.Side) (m : ℕ) :
          (ρ.part rest v m).childPositions.length < ρ.childPositions.length :=
        Ctx.Context.part_rest_childPositions_length_lt_of_mem_blocks hb v m
      have hc : 1 ≤ ρ.k - 1 - d ∧ ρ.k - 1 - d ≤ ρ.k - 2 := by omega
      have hPair (keep rest : List ℕ) (m c : ℕ)
          (hm : 1 ≤ m) (hmk : m ≤ ρ.k - 2) (hc : 1 ≤ c) (hck : c ≤ ρ.k - 2)
          (hKS : ∀ v c, (ρ.part keep v c).childPositions.length < ρ.childPositions.length)
          (hRS : ∀ v c, (ρ.part rest v c).childPositions.length < ρ.childPositions.length)
          (hp : 0 < (ρ.part keep Ctx.Side.lower m).bound + (ρ.part rest Ctx.Side.upper c).bound) :
          Witness ρ := by
        cases hs : s with
        | lower =>
          have ht : t = Ctx.Side.upper := by
            cases t with
            | lower => exact (hne hs).elim
            | upper => rfl
          obtain ⟨r, hr, hnot⟩ := hRemoved ρ rest Ctx.Side.upper c (hRS _ _)
          have hz := (hUnitZero ρ hPos Ctx.Side.upper
            (by simpa only [ht] using hUnit) rest c r hr hnot).2
          have hChosen : 0 < (ρ.part keep Ctx.Side.lower m).bound := by
            rw [hz, Nat.add_zero] at hp
            exact hp
          exact hRecurse keep m hm hmk (by simpa only [hs] using hKS Ctx.Side.lower m)
            (by simpa only [hs] using hChosen)
        | upper =>
          have ht : t = Ctx.Side.lower := by
            cases t with
            | lower => rfl
            | upper => exact (hne hs).elim
          obtain ⟨r, hr, hnot⟩ := hRemoved ρ keep Ctx.Side.lower m (hKS _ _)
          have hz := (hUnitZero ρ hPos Ctx.Side.lower
            (by simpa only [ht] using hUnit) keep m r hr hnot).2
          have hChosen : 0 < (ρ.part rest Ctx.Side.upper c).bound := by
            rw [hz, Nat.zero_add] at hp
            exact hp
          exact hRecurse rest c hc hck (by simpa only [hs] using hRS Ctx.Side.upper c)
            (by simpa only [hs] using hChosen)
      rcases hatt with hatt | hatt
      · apply hPair block rest d (ρ.k - 1 - d) hd hdk hc.1 hc.2 hBsmall hRsmall
        rw [← hatt]
        exact hBound
      · apply hPair rest block d (ρ.k - 1 - d) hd hdk hc.1 hc.2 hRsmall hBsmall
        rw [Nat.add_comm, ← hatt]
        exact hBound
  exact hmain σ.childPositions.length σ rfl hpositive hunit hbound

end ErdosSzekeres
