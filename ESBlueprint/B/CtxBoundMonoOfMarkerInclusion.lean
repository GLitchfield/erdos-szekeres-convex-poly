import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A recursive comparison principle for indexed marker inclusion. With common child pattern, word length, depth and k, preserving indexed level sides while deleting marker positions, lowering sibling maxima and increasing a/u can only increase all cup/cap limits and every fuel approximation of the recursive bound. Positive external labels in both contexts suffice. The proof transports extension witnesses by skipping unused levels and preserves the comparison through arbitrary parts, including empty new levels. Extends identical-word maximum domination and supports thinning external histories to essential markers in the unresolved sandwich and gap comparisons.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_mono_of_marker_inclusion (σ τ : Ctx.Context)
  (hσpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (hτpositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (ha : σ.a ≤ τ.a) (hu : σ.u ≤ τ.u) (hk : σ.k = τ.k)
  (hword : σ.word.length = τ.word.length)
  (hchild : ∀ p, σ.letterAt p = Ctx.Letter.child ↔ τ.letterAt p = Ctx.Letter.child)
  (hdepth : σ.maxima.length = τ.maxima.length)
  (hhistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧
    τ.extPositions j ⊆ σ.extPositions j ∧ τ.maximumAt j ≤ σ.maximumAt j) :
  (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let Sim (ρ υ : Context) : Prop :=
    ρ.a ≤ υ.a ∧ ρ.u ≤ υ.u ∧ ρ.k = υ.k ∧ ρ.word.length = υ.word.length ∧
    (∀ p, ρ.letterAt p = Letter.child ↔ υ.letterAt p = Letter.child) ∧
    ρ.maxima.length = υ.maxima.length ∧
    (∀ j ∈ ρ.levels, υ.sideAt j = ρ.sideAt j ∧
      υ.extPositions j ⊆ ρ.extPositions j ∧ υ.maximumAt j ≤ ρ.maximumAt j) ∧
    (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j)
  have hInitial : Sim σ τ := ⟨ha, hu, hk, hword, hchild, hdepth, hhistory, hσpositive, hτpositive⟩
  have hK {ρ υ : Context} (h : Sim ρ υ) : υ.k = ρ.k := h.2.2.1.symm
  have hChild {ρ υ : Context} (h : Sim ρ υ) : υ.childPositions = ρ.childPositions := by
    rcases h with ⟨_, _, _, hlen, hletters, _⟩
    simp only [childPositions, hlen, hletters]
  have hRuns {ρ υ : Context} (h : Sim ρ υ) : υ.numRuns = ρ.numRuns := by
    rcases h with ⟨_, _, _, hlen, hletters, _⟩
    simp only [numRuns, hlen, ne_eq, hletters]
  have hBlocks {ρ υ : Context} (h : Sim ρ υ) : υ.blocks = ρ.blocks := by
    simp only [blocks, hChild h]
  have hLevels {ρ υ : Context} (h : Sim ρ υ) : υ.levels = ρ.levels := by
    rcases h with ⟨_, _, _, _, _, hdepth, _⟩
    simp only [levels, hdepth]
  have hHistory {ρ υ : Context} (h : Sim ρ υ) (j : ℕ) (hj : j ∈ ρ.levels) :
      υ.sideAt j = ρ.sideAt j ∧ υ.extPositions j ⊆ ρ.extPositions j ∧
      υ.maximumAt j ≤ ρ.maximumAt j := h.2.2.2.2.2.2.1 j hj
  have hLevelsOn {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top : ℕ) :
      υ.levelsOn v top = ρ.levelsOn v top := by
    simp only [levelsOn, hLevels h]
    apply List.filter_congr
    intro j hj
    rw [(hHistory h j hj).1]
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hLeftWitness (ρ υ : Context) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j) →
      ∀ p q c d : ℕ, p ≤ q → c ≤ d →
      ∃ ks : List ℕ, ks.Sublist ls ∧
        (ls.foldl (leftStep υ) (p, c)).1 ≤ (ks.foldl (leftStep ρ) (q, d)).1 ∧
        (ls.foldl (leftStep υ) (p, c)).2 ≤ (ks.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil =>
      intro _ p q c d hpq hcd
      exact ⟨[], List.Sublist.refl _, hpq, hcd⟩
    | cons j ls ih =>
      intro hext p q c d hpq hcd
      have hrest : ∀ i ∈ ls, υ.extPositions i ⊆ ρ.extPositions i :=
        fun i hi => hext i (List.mem_cons_of_mem _ hi)
      cases hx : ((υ.extPositions j).filter (· < p)).getLast? with
      | none =>
        obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest p q c d hpq hcd
        refine ⟨ks, hks.cons j, ?_⟩
        simpa only [List.foldl_cons, leftStep, hx] using And.intro hends hcounts
      | some x =>
        have hxmem := List.mem_of_mem_getLast? (Option.mem_def.mpr hx)
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hxmem).2
        have hxq : x ∈ (ρ.extPositions j).filter (· < q) :=
          List.mem_filter.mpr ⟨hext j (by simp) (List.mem_filter.mp hxmem).1,
            by simp only [decide_eq_true_eq]; omega⟩
        have hnonempty := List.ne_nil_of_mem hxq
        let y := ((ρ.extPositions j).filter (· < q)).getLast hnonempty
        have hy : ((ρ.extPositions j).filter (· < q)).getLast? = some y :=
          List.getLast?_eq_some_getLast hnonempty
        have hxy : x ≤ y := ((hSort ρ j).filter _).rel_getLast hxq
        obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest x y (c + 1) (d + 1) hxy (by omega)
        refine ⟨j :: ks, hks.cons_cons j, ?_⟩
        simpa only [List.foldl_cons, leftStep, hx, hy] using And.intro hends hcounts
  have hRightWitness (ρ υ : Context) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j) →
      ∀ p q c d : ℕ, q ≤ p → c ≤ d →
      ∃ ks : List ℕ, ks.Sublist ls ∧
        (ks.foldl (rightStep ρ) (q, d)).1 ≤ (ls.foldl (rightStep υ) (p, c)).1 ∧
        (ls.foldl (rightStep υ) (p, c)).2 ≤ (ks.foldl (rightStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil =>
      intro _ p q c d hqp hcd
      exact ⟨[], List.Sublist.refl _, hqp, hcd⟩
    | cons j ls ih =>
      intro hext p q c d hqp hcd
      have hrest : ∀ i ∈ ls, υ.extPositions i ⊆ ρ.extPositions i :=
        fun i hi => hext i (List.mem_cons_of_mem _ hi)
      cases hx : ((υ.extPositions j).filter (p < ·)).head? with
      | none =>
        obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest p q c d hqp hcd
        refine ⟨ks, hks.cons j, ?_⟩
        simpa only [List.foldl_cons, rightStep, hx] using And.intro hends hcounts
      | some x =>
        have hxmem := List.mem_of_mem_head? (Option.mem_def.mpr hx)
        have hpx : p < x := of_decide_eq_true (List.mem_filter.mp hxmem).2
        have hxq : x ∈ (ρ.extPositions j).filter (q < ·) :=
          List.mem_filter.mpr ⟨hext j (by simp) (List.mem_filter.mp hxmem).1,
            by simp only [decide_eq_true_eq]; omega⟩
        have hnonempty := List.ne_nil_of_mem hxq
        let y := ((ρ.extPositions j).filter (q < ·)).head hnonempty
        have hy : ((ρ.extPositions j).filter (q < ·)).head? = some y :=
          List.head?_eq_some_head hnonempty
        have hyx : y ≤ x := ((hSort ρ j).filter _).rel_head hxq
        obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest x y (c + 1) (d + 1) hyx (by omega)
        refine ⟨j :: ks, hks.cons_cons j, ?_⟩
        simpa only [List.foldl_cons, rightStep, hx, hy] using And.intro hends hcounts
  have hLeft {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top p : ℕ) :
      υ.leftExt v top p ≤ ρ.leftExt v top p := by
    simp only [leftExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub : ls.Sublist (ρ.levelsOn v top) := by
      simpa only [hLevelsOn h] using List.mem_sublists.mp hls
    have hext : ∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j :=
      fun j hj => (hHistory h j (List.mem_filter.mp (hsub.subset hj)).1).2.1
    obtain ⟨ks, hks, _, hcount⟩ := hLeftWitness ρ υ ls hext p p 0 0 le_rfl le_rfl
    exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr (hks.trans hsub), rfl⟩, hcount⟩
  have hRight {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top p : ℕ) :
      υ.rightExt v top p ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub : ls.Sublist (ρ.levelsOn v top) := by
      simpa only [hLevelsOn h] using List.mem_sublists.mp hls
    have hext : ∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j :=
      fun j hj => (hHistory h j (List.mem_filter.mp (hsub.subset hj)).1).2.1
    obtain ⟨ks, hks, _, hcount⟩ := hRightWitness ρ υ ls hext p p 0 0 le_rfl le_rfl
    exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr (hks.trans hsub), rfl⟩, hcount⟩
  have hChain {ρ υ : Context} (h : Sim ρ υ) (v : Side) (p q : ℕ) :
      υ.chainExt v p q ≤ ρ.chainExt v p q :=
    Nat.add_le_add (hLeft h v 0 p) (hRight h v 0 q)
  have hJoin {ρ υ : Context} (h : Sim ρ υ) (v : Side) (p q : ℕ) :
      υ.joinExt v p q ≤ ρ.joinExt v p q := by
    unfold joinExt
    apply max_le_max (hChain h v p q)
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjρ : j ∈ ρ.levelsOn v 0 := by simpa only [hLevelsOn h] using hj
    have hmax := (hHistory h j (List.mem_filter.mp hjρ).1).2.2
    exact ⟨_, List.mem_map.mpr ⟨j, hjρ, rfl⟩,
      Nat.add_le_add (Nat.add_le_add (hLeft h v j p) (hRight h v j q)) hmax⟩
  have hLimits {ρ υ : Context} (h : Sim ρ υ) (p q : ℕ) :
      ρ.cupLimit p q ≤ υ.cupLimit p q ∧ ρ.capLimit p q ≤ υ.capLimit p q := by
    have hcl := hChain h Side.lower p q
    have hcu := hChain h Side.upper p q
    have hjl := hJoin h Side.lower p q
    have hju := hJoin h Side.upper p q
    have ha : ρ.a ≤ υ.a := h.1
    have hu : ρ.u ≤ υ.u := h.2.1
    simp only [cupLimit, capLimit, hK h]
    omega
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ p j s, (ρ.part keep v m).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ p by rw [part_word_length]; omega)
      rw [hn] at hp
      cases hp
    cases he : ρ.letterAt p with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hpl he] at hp
      split at hp
      · cases hp
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hpl he] at hp
      cases hp
      omega
  have hPartChildAt {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m p : ℕ) :
      (ρ.part keep v m).letterAt p = Letter.child ↔
        (υ.part keep v m).letterAt p = Letter.child := by
    rcases h with ⟨_, _, _, hlen, hletters, _⟩
    by_cases hpl : p < ρ.word.length
    · have hpu : p < υ.word.length := by omega
      cases hr : ρ.letterAt p with
      | child =>
        have hs : υ.letterAt p = Letter.child := (hletters p).mp hr
        rw [part_letterAt_of_child ρ keep v m hpl hr, part_letterAt_of_child υ keep v m hpu hs]
      | ext j s =>
        have hs : υ.letterAt p ≠ Letter.child := by
          intro hc
          have he := (hletters p).mpr hc
          rw [hr] at he
          cases he
        cases ht : υ.letterAt p with
        | child => exact False.elim (hs ht)
        | ext i t =>
          rw [part_letterAt_of_ext ρ keep v m hpl hr, part_letterAt_of_ext υ keep v m hpu ht]
          simp
    · have hpρ : (ρ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
      have hpυ : (υ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
      rw [letterAt_of_length_le (ρ.part keep v m) hpρ, letterAt_of_length_le (υ.part keep v m) hpυ]
  have hPart {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m : ℕ) :
      Sim (ρ.part keep v m) (υ.part keep v m) := by
    have hSaved := h
    obtain ⟨ha, hu, hk, hlen, hletters, hdepth, hhist, hρpos, hυpos⟩ := h
    refine ⟨ha, hu, hk, ?_, fun p => hPartChildAt hSaved keep v m p, ?_, ?_,
      hPartPositive ρ keep v m, hPartPositive υ keep v m⟩
    · simpa only [part_word_length] using hlen
    · change (m :: ρ.maxima).length = (m :: υ.maxima).length
      simp only [List.length_cons, hdepth]
    · intro j hj
      have hj' : j ∈ 1 :: ρ.levels.map (· + 1) := by simpa only [part_levels] using hj
      rcases List.mem_cons.mp hj' with hjone | hjold
      · subst j
        have hExtOne : (υ.part keep v m).extPositions 1 = (ρ.part keep v m).extPositions 1 := by
          rw [part_extPositions_one hυpos, part_extPositions_one hρpos, hChild hSaved]
        have hSideOne : (υ.part keep v m).sideAt 1 = (ρ.part keep v m).sideAt 1 := by
          by_cases hempty : (ρ.part keep v m).extPositions 1 = []
          · simp only [sideAt, hExtOne, hempty, List.head?_nil]
          · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hempty
            have hpυ : p ∈ (υ.part keep v m).extPositions 1 := by simpa only [hExtOne] using hp
            rw [part_sideAt_one_of_mem hυpos keep v m hpυ, part_sideAt_one_of_mem hρpos keep v m hp]
        refine ⟨hSideOne, ?_, ?_⟩
        · intro p hp
          simpa only [hExtOne] using hp
        · simp only [part_maximumAt_one, le_refl]
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hjold
        have hi1 := one_le_of_mem_levels hi
        simpa only [part_sideAt_succ ρ keep v m hi1, part_sideAt_succ υ keep v m hi1,
          part_extPositions_succ ρ keep v m hi1, part_extPositions_succ υ keep v m hi1,
          part_maximumAt_succ ρ keep v m hi1, part_maximumAt_succ υ keep v m hi1] using hhist i hi
  have hBase {ρ υ : Context} (h : Sim ρ υ) : ρ.base ≤ υ.base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild h]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      simpa only [hK h] using baseOf_mono (k := ρ.k) (hLimits h p p).1 (hLimits h p p).2
  have hFuel : ∀ fuel (ρ υ : Context), Sim ρ υ → boundFuel fuel ρ ≤ boundFuel fuel υ := by
    intro fuel
    induction fuel with
    | zero => intro ρ υ _; exact le_rfl
    | succ fuel ih =>
      intro ρ υ h
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel (υ.part keep v m) :=
        ih _ _ (hPart h keep v m)
      simp only [boundFuel, hRuns h, hChild h, hBlocks h, hK h]
      split_ifs
      · exact hBase h
      · apply Ctx.getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, hkeep, d, hd, hx⟩ := hx
        rcases hx with rfl | rfl
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inl rfl⟩
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inr rfl⟩
  refine ⟨fun p q => hLimits hInitial p q, fun fuel => hFuel fuel σ τ hInitial, ?_⟩
  simpa only [bound, hChild hInitial] using hFuel (σ.childPositions.length + 1) σ τ hInitial

end ErdosSzekeres
