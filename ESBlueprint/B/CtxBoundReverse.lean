import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxReverseExtensionTransport
import ESBlueprint.B.CtxPointLimitsEqOfChildInterval

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Reversing the word of any well-formed context preserves its recursive bound, with parameters, levels, sides and maxima unchanged. Supplies reflection for the singleton-end sandwich and future context-bound arguments; includes the empty and single-run cases.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_reverse_extension_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_reverse (σ : Ctx.Context) (hwf : σ.WellFormed) : ({ σ with word := σ.word.reverse } : Ctx.Context).bound = σ.bound := by
  classical
  let rev (τ : Ctx.Context) : Ctx.Context := { τ with word := τ.word.reverse }
  let flip (τ : Ctx.Context) (p : ℕ) := τ.word.length - 1 - p
  have hrev : ∀ τ, rev (rev τ) = τ := by
    intro τ
    cases τ
    simp [rev]
  have hlt : ∀ τ p, p < τ.word.length → flip τ p < τ.word.length := by
    intro τ p hp
    dsimp [flip]
    omega
  have hinv : ∀ τ p, p < τ.word.length → flip τ (flip τ p) = p := by
    intro τ p hp
    dsimp [flip]
    omega
  have hletter : ∀ τ p, p < τ.word.length →
      (rev τ).letterAt (flip τ p) = τ.letterAt p := by
    intro τ p hp
    simp only [Ctx.Context.letterAt, rev, List.getElem?_reverse (hlt τ p hp)]
    change τ.word[flip τ (flip τ p)]?.getD Ctx.Letter.child =
      τ.word[p]?.getD Ctx.Letter.child
    rw [hinv τ p hp]
  have hrange : ∀ τ, (List.range τ.word.length).reverse.map (flip τ) =
      List.range τ.word.length := by
    intro τ
    have h : (List.range τ.word.length).map (flip τ) =
        (List.range τ.word.length).reverse := by
      simpa [flip, ← List.range_eq_range'] using
        (List.reverse_range' (s := 0) (n := τ.word.length)).symm
    rw [List.map_reverse, h, List.reverse_reverse]
  have hchild : ∀ τ, (rev τ).childPositions =
      τ.childPositions.reverse.map (flip τ) := by
    intro τ
    unfold Ctx.Context.childPositions
    simp only [rev, List.length_reverse]
    calc
      _ = ((List.range τ.word.length).reverse.map (flip τ)).filter
          (fun p => decide ((rev τ).letterAt p = Ctx.Letter.child)) := by rw [hrange]
      _ = ((List.range τ.word.length).filter (fun p =>
          decide ((rev τ).letterAt (flip τ p) = Ctx.Letter.child))).reverse.map
          (flip τ) := by rw [List.filter_map, List.filter_reverse]; rfl
      _ = _ := by
        congr 2
        apply List.filter_congr
        intro p hp
        rw [hletter τ p (List.mem_range.mp hp)]
  have hchildLen : ∀ τ, (rev τ).childPositions.length = τ.childPositions.length := by
    intro τ
    rw [hchild]
    simp
  have hmem : ∀ (τ : Ctx.Context) p, p ∈ τ.childPositions → p < τ.word.length := by
    intro τ p hp
    exact List.mem_range.mp (List.mem_filter.mp hp).1
  have hkeepMem : ∀ τ (keep : List ℕ), (∀ p ∈ keep, p < τ.word.length) →
      ∀ p, p < τ.word.length →
        (flip τ p ∈ keep.reverse.map (flip τ) ↔ p ∈ keep) := by
    intro τ keep hk p hp
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨q, hq, he⟩
      have hi := congrArg (flip τ) he
      rw [hinv τ q (hk q hq), hinv τ p hp] at hi
      simpa [hi] using hq
    · intro hpk
      exact ⟨p, hpk, rfl⟩
  have hpart : ∀ τ (keep : List ℕ), (∀ p ∈ keep, p < τ.word.length) →
      ∀ s m, rev (τ.part keep s m) =
        (rev τ).part (keep.reverse.map (flip τ)) s m := by
    intro τ keep hk s m
    let f (p : ℕ) := match τ.letterAt p with
      | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child else Ctx.Letter.ext 1 s
      | Ctx.Letter.ext l v => Ctx.Letter.ext (l + 1) v
    let g (p : ℕ) := match (rev τ).letterAt p with
      | Ctx.Letter.child => if p ∈ keep.reverse.map (flip τ) then
          Ctx.Letter.child else Ctx.Letter.ext 1 s
      | Ctx.Letter.ext l v => Ctx.Letter.ext (l + 1) v
    have hfg : ∀ p ∈ List.range τ.word.length, g (flip τ p) = f p := by
      intro p hp
      have hp' := List.mem_range.mp hp
      dsimp only [f, g]
      rw [hletter τ p hp']
      cases τ.letterAt p with
      | child => simp only [hkeepMem τ keep hk p hp']
      | ext l v => rfl
    have hw : ((List.range τ.word.length).map f).reverse =
        (List.range (rev τ).word.length).map g := by
      simp only [rev, List.length_reverse]
      calc
        _ = (List.range τ.word.length).reverse.map f := List.map_reverse.symm
        _ = (List.range τ.word.length).reverse.map (fun p => g (flip τ p)) := by
          apply List.map_congr_left
          intro p hp
          exact (hfg p (List.mem_reverse.mp hp)).symm
        _ = ((List.range τ.word.length).reverse.map (flip τ)).map g := by rw [List.map_map]; rfl
        _ = _ := by rw [hrange]
    cases τ
    simp only [rev, Ctx.Context.part]
    congr 1
  have hrest : ∀ τ (keep : List ℕ), (∀ p ∈ keep, p < τ.word.length) →
      (τ.childPositions.filter (· ∉ keep)).reverse.map (flip τ) =
        (rev τ).childPositions.filter (· ∉ keep.reverse.map (flip τ)) := by
    intro τ keep hk
    rw [hchild, List.filter_map, List.filter_reverse]
    congr 2
    apply List.filter_congr
    intro p hp
    simp only [Function.comp_def, decide_eq_decide]
    exact not_congr (hkeepMem τ keep hk p (hmem τ p hp)).symm
  have hblockData : ∀ (τ : Ctx.Context) (keep : List ℕ), keep ∈ τ.blocks →
      keep ≠ [] ∧ keep.length < τ.childPositions.length ∧ keep <:+: τ.childPositions := by
    intro τ keep hk
    simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
      List.mem_range, List.mem_map, decide_eq_true_eq] at hk
    obtain ⟨⟨i, hi, l, hl, rfl⟩, hlen⟩ := hk
    refine ⟨?_, hlen, ?_⟩
    · have hd : 0 < (τ.childPositions.drop i).length := by
        simp only [List.length_drop]
        omega
      apply List.ne_nil_of_length_pos
      simp only [List.length_take]
      omega
    · refine ⟨τ.childPositions.take i, (τ.childPositions.drop i).drop (l+1), ?_⟩
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have hblock : ∀ τ (keep : List ℕ), keep ∈ τ.blocks →
      keep.reverse.map (flip τ) ∈ (rev τ).blocks := by
    intro τ keep hk
    obtain ⟨hne, hlen, hInfix⟩ := hblockData τ keep hk
    have h : keep.reverse.map (flip τ) <:+: (rev τ).childPositions := by
      rw [hchild]
      exact hInfix.reverse.map (flip τ)
    obtain ⟨pre, post, he⟩ := h
    have hlength := congrArg List.length he
    simp only [List.length_append] at hlength
    have hpos : 0 < (keep.reverse.map (flip τ)).length := by
      simpa using List.length_pos_iff.mpr hne
    have hproper : (keep.reverse.map (flip τ)).length < (rev τ).childPositions.length := by
      simpa only [List.length_map, List.length_reverse, hchildLen] using hlen
    simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
      List.mem_range, List.mem_map, decide_eq_true_eq]
    refine ⟨⟨pre.length, by omega, (keep.reverse.map (flip τ)).length - 1,
      by omega, ?_⟩, hproper⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ (keep.reverse.map (flip τ)).length)]
    have hslice : ((pre ++ keep.reverse.map (flip τ) ++ post).drop pre.length).take
        (keep.reverse.map (flip τ)).length = keep.reverse.map (flip τ) := by
      simp [List.append_assoc]
    exact (congrArg (fun xs : List ℕ => (xs.drop pre.length).take
      (keep.reverse.map (flip τ)).length) he).symm.trans hslice
  let Convex (τ : Ctx.Context) := ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions,
    ∀ r, p ≤ r → r ≤ q → r ∈ τ.childPositions
  have hconvex : ∀ τ, τ.numRuns ≤ 1 → Convex τ := by
    intro τ hruns p hp q hq r hpr hrq
    have hchildNe : τ.childPositions ≠ [] := List.ne_nil_of_mem hp
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ τ.childPositions := by rw [hcons]; exact List.mem_cons_self
    have hordered : τ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise τ).imp le_of_lt
    have hmin : ∀ p ∈ τ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range τ.word.length).filter fun p =>
      τ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hstartsLen : starts.length ≤ 1 := by simpa [starts, Ctx.Context.numRuns] using hruns
    have hstartsNodup : starts.Nodup := List.nodup_range.filter _
    have hbRange : b < τ.word.length := hmem τ b hb
    have hbLetter : τ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition : b = 0 ∨ τ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro hprev
        have hprevMem : b - 1 ∈ τ.childPositions := by
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
      have htwo : ({b, p} : Finset ℕ).card = 2 := by simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ τ.childPositions, p ≠ b → p - 1 ∈ τ.childPositions := by
      intro p hp hpb
      have hpRange : p < τ.word.length := hmem τ p hp
      have hpLetter : τ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by have := hmin p hp; omega
      by_contra hprevMem
      have hprevLetter : τ.letterAt (p - 1) ≠ Ctx.Letter.child := by
        intro hletter
        apply hprevMem
        apply List.mem_filter.2
        exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
      have hpStart : p ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
      exact hpb (hstartUnique p hpStart)
    have hfill : ∀ p ∈ τ.childPositions, ∀ q, b ≤ q → q ≤ p →
        q ∈ τ.childPositions := by
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
    exact hfill q hq r ((hmin p hp).trans hpr) hrq
  have hconvexRuns : ∀ τ, Convex τ → τ.numRuns ≤ 1 := by
    intro τ hc
    by_cases hnil : τ.childPositions = []
    · have h := Ctx.numRuns_le_length τ
      rw [hnil] at h
      simpa using h.trans (by decide : 0 ≤ 1)
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hnil
    have hb : b ∈ τ.childPositions := by rw [hcons]; exact List.mem_cons_self
    have hordered : τ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise τ).imp le_of_lt
    have hmin : ∀ p ∈ τ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range τ.word.length).filter fun p =>
      τ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hsubset : starts.toFinset ⊆ ({b} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child) := by simpa [starts] using hp
      have hpchild : p ∈ τ.childPositions := by
        simp only [Ctx.Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hstart.1, hstart.2.1⟩
      have hbp := hmin p hpchild
      simp only [Finset.mem_singleton]
      by_contra hpb
      have hprev : p - 1 ∈ τ.childPositions :=
        hc b hb p hpchild (p - 1) (by omega) (by omega)
      have hprevLetter : τ.letterAt (p - 1) = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hprev).2
      rcases hstart.2.2 with hz | hn
      · omega
      · exact hn hprevLetter
    calc
      τ.numRuns = starts.toFinset.card :=
        (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
      _ ≤ ({b} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 1 := by simp
  have hchildMem : ∀ τ p, p < τ.word.length →
      (flip τ p ∈ (rev τ).childPositions ↔ p ∈ τ.childPositions) := by
    intro τ p hp
    rw [hchild]
    exact hkeepMem τ τ.childPositions (hmem τ) p hp
  have hchildBack : ∀ τ p, p ∈ (rev τ).childPositions → flip τ p ∈ τ.childPositions := by
    intro τ p hp
    have hp' : p < τ.word.length := by simpa [rev] using hmem (rev τ) p hp
    apply (hchildMem τ (flip τ p) (hlt τ p hp')).mp
    rw [hinv τ p hp']
    exact hp
  have hrunReverse : ∀ τ, τ.numRuns ≤ 1 → (rev τ).numRuns ≤ 1 := by
    intro τ hr
    apply hconvexRuns
    intro p hp q hq r hpr hrq
    have hp' : p < τ.word.length := by simpa [rev] using hmem (rev τ) p hp
    have hq' : q < τ.word.length := by simpa [rev] using hmem (rev τ) q hq
    have hr' : r < τ.word.length := by omega
    have h := hconvex τ hr (flip τ q) (hchildBack τ q hq)
      (flip τ p) (hchildBack τ p hp) (flip τ r)
      (by dsimp [flip]; omega) (by dsimp [flip]; omega)
    simpa only [hinv τ r hr'] using
      (hchildMem τ (flip τ r) (hlt τ r hr')).mpr h
  have hruns : ∀ τ, (rev τ).numRuns ≤ 1 ↔ τ.numRuns ≤ 1 := by
    intro τ
    constructor
    · intro hr
      simpa only [hrev] using hrunReverse (rev τ) hr
    · exact hrunReverse τ
  have hcapacities : ∀ (τ : Ctx.Context), τ.numRuns ≤ 1 → ∀ p ∈ τ.childPositions,
      ∀ q ∈ τ.childPositions,
        τ.cupLimit p p = τ.cupLimit q q ∧ τ.capLimit p p = τ.capLimit q q := by
    intro τ hr p hp q hq
    rcases le_total p q with hpq | hqp
    · exact ctx_point_limits_eq_of_child_interval τ p q hp hq hpq
        (hconvex τ hr p hp q hq)
    · have h := ctx_point_limits_eq_of_child_interval τ q p hq hp hqp
        (hconvex τ hr q hq p hp)
      exact ⟨h.1.symm, h.2.symm⟩
  have hbase : ∀ τ, τ.WellFormed → τ.numRuns ≤ 1 → (rev τ).base = τ.base := by
    intro τ hw hr
    rw [Ctx.Context.base_eq_baseOf, Ctx.Context.base_eq_baseOf]
    cases hp : τ.childPositions.head? with
    | none =>
      have hnil : τ.childPositions = [] := List.head?_eq_none_iff.mp hp
      have hnil' : (rev τ).childPositions = [] := by rw [hchild, hnil]; rfl
      simp only [hnil', List.head?_nil]
    | some p =>
      have hpm : p ∈ τ.childPositions := List.mem_of_mem_head? (Option.mem_def.mpr hp)
      cases hq : (rev τ).childPositions.head? with
      | none =>
        have hnil' : (rev τ).childPositions = [] := List.head?_eq_none_iff.mp hq
        have hlen := hchildLen τ
        rw [hnil', List.length_nil] at hlen
        have hnil : τ.childPositions = [] := List.eq_nil_of_length_eq_zero hlen.symm
        simp only [hnil, List.not_mem_nil] at hpm
      | some q =>
        have hqm : q ∈ (rev τ).childPositions := List.mem_of_mem_head? (Option.mem_def.mpr hq)
        have hq' : q < τ.word.length := by simpa [rev] using hmem (rev τ) q hqm
        have hold := hchildBack τ q hqm
        have hc := hcapacities τ hr (flip τ q) hold p hpm
        have ht := (ctx_reverse_extension_transport τ hw).2.2
          (flip τ q) (flip τ q) (hlt τ q hq') (hlt τ q hq')
        change (rev τ).cupLimit (flip τ (flip τ q)) (flip τ (flip τ q)) =
            τ.cupLimit (flip τ q) (flip τ q) ∧
          (rev τ).capLimit (flip τ (flip τ q)) (flip τ (flip τ q)) =
            τ.capLimit (flip τ q) (flip τ q) at ht
        rw [hinv τ q hq'] at ht
        simp only [ht.1, ht.2, hc.1, hc.2]
        rfl
  have hFuel : ∀ fuel (τ : Ctx.Context), τ.WellFormed →
      Ctx.Context.boundFuel fuel τ ≤ Ctx.Context.boundFuel fuel (rev τ) := by
    intro fuel
    induction fuel with
    | zero => intro τ hw; exact le_rfl
    | succ fuel ih =>
      intro τ hw
      simp only [Ctx.Context.boundFuel]
      by_cases hr : τ.numRuns ≤ 1
      · rw [if_pos hr, if_pos ((hruns τ).mpr hr)]
        exact le_of_eq (hbase τ hw hr).symm
      · rw [if_neg hr, if_neg (fun h => hr ((hruns τ).mp h))]
        apply Ctx.getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, hk, d, hd, hx⟩ := hx
        have hd' : d < τ.k - 2 := List.mem_range.mp hd
        have hm1 : 1 ≤ d + 1 := by omega
        have hmk : d + 1 ≤ τ.k - 2 := by omega
        have hc1 : 1 ≤ τ.k - 1 - (d + 1) := by omega
        have hck : τ.k - 1 - (d + 1) ≤ τ.k - 2 := by omega
        have hkbound : ∀ p ∈ keep, p < τ.word.length := by
          intro p hp
          exact hmem τ p ((hblockData τ keep hk).2.2.sublist.subset hp)
        have hrestbound : ∀ p ∈ τ.childPositions.filter (· ∉ keep),
            p < τ.word.length := by
          intro p hp
          exact hmem τ p (List.mem_filter.mp hp).1
        have hParts (s : Ctx.Side) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ τ.k - 2) :
            Ctx.Context.boundFuel fuel (τ.part keep s m) ≤
              Ctx.Context.boundFuel fuel ((rev τ).part (keep.reverse.map (flip τ)) s m) := by
          have h := ih (τ.part keep s m) (hw.part keep s hm hmk)
          rw [hpart τ keep hkbound] at h
          exact h
        have hOther (s : Ctx.Side) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ τ.k - 2) :
            Ctx.Context.boundFuel fuel (τ.part (τ.childPositions.filter (· ∉ keep)) s m) ≤
              Ctx.Context.boundFuel fuel ((rev τ).part
                ((rev τ).childPositions.filter (· ∉ keep.reverse.map (flip τ))) s m) := by
          have h := ih (τ.part (τ.childPositions.filter (· ∉ keep)) s m)
            (hw.part _ s hm hmk)
          rw [hpart τ _ hrestbound, hrest τ keep hkbound] at h
          exact h
        rcases hx with rfl | rfl
        · refine ⟨_, ?_, Nat.add_le_add (hParts .lower _ hm1 hmk) (hOther .upper _ hc1 hck)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep.reverse.map (flip τ), hblock τ keep hk, d, hd, Or.inl rfl⟩
        · refine ⟨_, ?_, Nat.add_le_add (hParts .upper _ hc1 hck) (hOther .lower _ hm1 hmk)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep.reverse.map (flip τ), hblock τ keep hk, d, hd, Or.inr rfl⟩
  have hFuelEq : ∀ fuel (τ : Ctx.Context), τ.WellFormed →
      Ctx.Context.boundFuel fuel (rev τ) = Ctx.Context.boundFuel fuel τ := by
    intro fuel τ hw
    apply Nat.le_antisymm
    · have h := hFuel fuel (rev τ) (ctx_reverse_extension_transport τ hw).1
      simpa only [hrev] using h
    · exact hFuel fuel τ hw
  change (rev σ).bound = σ.bound
  unfold Ctx.Context.bound
  rw [hchildLen]
  exact hFuelEq _ σ hwf


end ErdosSzekeres
