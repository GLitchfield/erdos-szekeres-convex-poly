import ESBlueprint.B.CtxPositiveBoundAttainedByIntervalCut
import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

namespace ErdosSzekeres

/-- One protected source child bracketed by two actual selected old markers annihilates every-fuel and full context bound when the chosen global axis is at most three and the opposite axis at most two. Raw positive actual external labels suffice for arbitrary history, without WF or legal maxima. Positive same-axis single-run leaf descent and the ordered two-level exterior lemma expose the unavoidable pure chain cost two, closing the protected-child gap in axis-two ROOT-NF.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_zero_of_protected_bracketed_child_and_opposite_unit_axis (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t)
    (hchosen : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2)
    (N : ℕ) (hN : N ∈ σ.levelsOn s 0)
    (x r y : ℕ) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions N)
    (hr : r ∈ σ.childPositions) (hxr : x < r) (hry : r < y) :
    (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
  classical
  have hLeaf (σ : Ctx.Context)
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
  have hProtectedCost (τ : Ctx.Context) (s : Ctx.Side) (N : ℕ) (hN : N ∈ τ.levelsOn s 0)
    (x r y : ℕ) (hx : x ∈ τ.extPositions N) (hy : y ∈ τ.extPositions N)
    (hxr : x < r) (hry : r < y)
    (hrsite : τ.letterAt r = Ctx.Letter.child ∨
      ∃ j, j ∈ τ.levelsOn s 0 ∧ j < N ∧ τ.letterAt r = Ctx.Letter.ext j s)
    (hruns : τ.numRuns ≤ 1) :
    ∀ p ∈ τ.childPositions, 2 ≤ τ.chainExt s p p := by
    classical
    -- Reuse accepted R18 raw one-run interval proof, then R15 ordered two-level fold witnesses.
    have hInterval (ρ : Ctx.Context) (hruns : ρ.numRuns ≤ 1)
        (hchildNe : ρ.childPositions ≠ []) :
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
    have hExtMem (q j : ℕ) (hq : q < τ.word.length)
        (he : τ.letterAt q = Ctx.Letter.ext j s) : q ∈ τ.extPositions j := by
      simp [Ctx.Context.extPositions, hq, he]
    have hOneLeft (j q p : ℕ) (hj : j ∈ τ.levelsOn s 0)
        (hq : q ∈ τ.extPositions j) (hqp : q < p) : 1 ≤ τ.leftExt s 0 p := by
      have hm : q ∈ (τ.extPositions j).filter (· < p) := by simp [hq, hqp]
      have hne := List.ne_nil_of_mem hm
      have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ τ.leftExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
        List.getLast?_eq_some_getLast hne] using hv
    have hOneRight (j q p : ℕ) (hj : j ∈ τ.levelsOn s 0)
        (hq : q ∈ τ.extPositions j) (hpq : p < q) : 1 ≤ τ.rightExt s 0 p := by
      have hm : q ∈ (τ.extPositions j).filter (p < ·) := by simp [hq, hpq]
      have hne := List.ne_nil_of_mem hm
      have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ τ.rightExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
        List.head?_eq_some_head hne] using hv
    have hyR : y < τ.word.length := List.mem_range.mp (List.mem_filter.mp hy).1
    have hrR : r < τ.word.length := by omega
    have hOldNotChild (q : ℕ) (hq : q ∈ τ.extPositions N) :
        τ.letterAt q ≠ Ctx.Letter.child := by
      intro hc
      simp [Ctx.Context.extPositions, hc] at hq
    rcases hrsite with hrChild | ⟨j, hj, hjN, hrExt⟩
    · have hrMem : r ∈ τ.childPositions := by
        simp [Ctx.Context.childPositions, hrR, hrChild]
      obtain ⟨b, hspan⟩ := hInterval τ hruns (List.ne_nil_of_mem hrMem)
      have hMem (q : ℕ) : q ∈ τ.childPositions ↔
          b ≤ q ∧ q < b + τ.childPositions.length := by
        rw [hspan]
        simpa only [List.length_range'] using
          (List.mem_range'_1 (m := q) (s := b) (n := τ.childPositions.length))
      have hrSpan := (hMem r).mp hrMem
      intro p hp
      have hpSpan := (hMem p).mp hp
      have hxp : x < p := by
        by_contra hn
        have hxMem : x ∈ τ.childPositions := (hMem x).mpr (by omega)
        exact hOldNotChild x hx (of_decide_eq_true (List.mem_filter.mp hxMem).2)
      have hpy : p < y := by
        by_contra hn
        have hyMem : y ∈ τ.childPositions := (hMem y).mpr (by omega)
        exact hOldNotChild y hy (of_decide_eq_true (List.mem_filter.mp hyMem).2)
      have hleft := hOneLeft N x p hN hx hxp
      have hright := hOneRight N y p hN hy hpy
      change 2 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p
      omega
    · have hrMem := hExtMem r j hrR hrExt
      have hJlevel : j ∈ τ.levels := (List.mem_filter.mp hj).1
      have hNlevel : N ∈ τ.levels := (List.mem_filter.mp hN).1
      have hJs : τ.sideAt j = s := (Ctx.Context.one_le_of_mem_levelsOn hj).2.2
      have hNs : τ.sideAt N = s := (Ctx.Context.one_le_of_mem_levelsOn hN).2.2
      intro p hp
      by_contra hn
      have hc : τ.chainExt s p p ≤ 1 := by omega
      rcases ctx_chain_one_children_exterior_of_two_levels
        τ s j N r x hJlevel hNlevel hjN hJs hNs hrMem hx with h | h
      · omega
      have hpx := h.2 p hp hc N hN x hx
      rcases ctx_chain_one_children_exterior_of_two_levels
        τ s j N r y hJlevel hNlevel hjN hJs hNs hrMem hy with h' | h'
      · have hyp := h'.2 p hp hc N hN y hy
        omega
      · omega
  have hfull : σ.bound = 0 := by
    by_contra hzero
    have hbound : 0 < σ.bound := by omega
    obtain ⟨τ, history, ha, hu, hk, hlen, hmaxτ, hlegal,
      hrunτ, hbase, hchildren, hword, hold, hnew⟩ :=
      hLeaf σ hpositive s t hne hunit hbound
    have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hN).1
    have hNside : σ.sideAt N = s := (Ctx.Context.one_le_of_mem_levelsOn hN).2.2
    have hNlen : N ≤ σ.maxima.length := by
      have hm := (List.mem_filter.mp hN).1
      simp only [Ctx.Context.levels, List.mem_map, List.mem_range] at hm
      obtain ⟨i, hi, he⟩ := hm
      omega
    let K := N + history.length
    have hKpos : 1 ≤ K := by dsimp [K]; omega
    have hKlen : K ≤ τ.maxima.length := by
      rw [hmaxτ, List.length_append]
      dsimp [K]
      omega
    have hK : K ∈ τ.levelsOn s 0 := by
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
        exact ⟨K - 1, by omega, by omega⟩
      · have hsK : τ.sideAt K = s := (hold N hNpos).trans hNside
        simp [hsK]
    have hOldMem (p : ℕ) (hp : p ∈ σ.extPositions N) : p ∈ τ.extPositions K := by
      have hpR : p < σ.word.length := List.mem_range.mp (List.mem_filter.mp hp).1
      cases he : σ.letterAt p with
      | child => simp [Ctx.Context.extPositions, he] at hp
      | ext j v =>
        have hj : j = N := by simpa [he] using (List.mem_filter.mp hp).2
        have hw := hword p hpR
        rw [he] at hw
        subst j
        have hwK : τ.letterAt p = Ctx.Letter.ext K v := by simpa only [K] using hw
        simp [Ctx.Context.extPositions, hlen, hpR, hwK]
    have hrR : r < σ.word.length := List.mem_range.mp (List.mem_filter.mp hr).1
    have hrC : σ.letterAt r = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.mp hr).2
    have hsite : τ.letterAt r = Ctx.Letter.child ∨
        ∃ j, j ∈ τ.levelsOn s 0 ∧ j < K ∧ τ.letterAt r = Ctx.Letter.ext j s := by
      have hw := hword r hrR
      rw [hrC] at hw
      rcases hw with h | ⟨j, hj, hjlen, he⟩
      · exact Or.inl h
      · refine Or.inr ⟨j, ?_, by dsimp [K]; omega, he⟩
        apply List.mem_filter.mpr
        refine ⟨?_, by simp [hnew j hj hjlen]⟩
        simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
        have hjlenτ : j ≤ τ.maxima.length := by
          rw [hmaxτ, List.length_append]
          omega
        exact ⟨j - 1, by omega, by omega⟩
    have hcost : ∀ p ∈ τ.childPositions, 2 ≤ τ.chainExt s p p :=
      hProtectedCost τ s K hK x r y (hOldMem x hx) (hOldMem y hy) hxr hry hsite hrunτ
    have hglobal : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.u | Ctx.Side.upper => τ.a) s ≤ 3 := by
      simpa only [ha, hu] using hchosen
    cases hc : τ.childPositions with
    | nil => simp [Ctx.Context.base, hc] at hbase
    | cons p ps =>
      have hp : p ∈ τ.childPositions := by rw [hc]; exact List.mem_cons_self
      have hpCost := hcost p hp
      cases hs : s with
      | lower =>
        have hg : τ.u ≤ 3 := by simpa only [hs] using hglobal
        have hge : 2 ≤ τ.chainExt Ctx.Side.lower p p := by simpa only [hs] using hpCost
        have hz : τ.u - 1 - τ.chainExt Ctx.Side.lower p p = 0 := by omega
        have hlim : τ.cupLimit p p = 0 := by
          simp only [Ctx.Context.cupLimit, hz, Nat.zero_min]
        simp [Ctx.Context.base, hc, hlim] at hbase
      | upper =>
        have hg : τ.a ≤ 3 := by simpa only [hs] using hglobal
        have hge : 2 ≤ τ.chainExt Ctx.Side.upper p p := by simpa only [hs] using hpCost
        have hz : τ.a - 1 - τ.chainExt Ctx.Side.upper p p = 0 := by omega
        have hlim : τ.capLimit p p = 0 := by
          simp only [Ctx.Context.capLimit, hz, Nat.zero_min]
        simp [Ctx.Context.base, hc, hlim] at hbase
  refine ⟨?_, hfull⟩
  intro fuel
  have hle := Ctx.Context.boundFuel_mono
    (Nat.le_max_left fuel (σ.childPositions.length + 1)) σ
  rw [Ctx.Context.boundFuel_eq_bound σ
    (Nat.le_max_right fuel (σ.childPositions.length + 1)), hfull] at hle
  exact Nat.eq_zero_of_le_zero hle

end ErdosSzekeres
