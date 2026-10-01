import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- A raw context with one indexed sibling maximum and a uniform child/ext1side word has the bound of its endpoint-presence normal word whenever it has at most one child run. Arbitrary globals, k and sibling maximum; no well-formedness or positivity hypotheses. Nonempty children occupy one interval, so endpoint marker presence determines the one-level extension folds and capacities. Empty support gives zero, and absent physical markers retain the default lower side and unused indexed maximum. Removes the single-run branch of root normal-form induction; multirun paired transport remains separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_one_level_single_run_bound_normal_form (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m]) (side : Ctx.Side)
    (hletters : ∀ x ∈ σ.word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side)
    (hruns : σ.numRuns ≤ 1) :
    let marker := Ctx.Letter.ext 1 side
    let normalWord :=
      (if σ.word.head? = some marker then [marker] else []) ++
      (List.replicate σ.numRuns Ctx.Letter.child).intersperse marker ++
      (if σ.word.getLast? = some marker then [marker] else [])
    σ.bound = ({σ with word := normalWord} : Ctx.Context).bound := by
  classical
  let marker := Ctx.Letter.ext 1 side
  have hmarker : Ctx.Letter.child ≠ marker := by simp [marker]
  let normalWord :=
    (if σ.word.head? = some marker then [marker] else []) ++
    (List.replicate σ.numRuns Ctx.Letter.child).intersperse marker ++
    (if σ.word.getLast? = some marker then [marker] else [])
  let τ : Ctx.Context := {σ with word := normalWord}
  change σ.bound = τ.bound
  have hemptyBound (ρ : Ctx.Context) (hρ : ρ.childPositions = []) : ρ.bound = 0 := by
    have hh : ρ.numRuns ≤ 1 := by
      have h := Ctx.numRuns_le_length ρ
      rw [hρ] at h
      simp only [List.length_nil] at h
      omega
    simp only [Ctx.Context.bound, hρ, List.length_nil, Nat.zero_add]
    rw [Ctx.Context.boundFuel.eq_2, if_pos hh]
    simp [Ctx.Context.base, hρ]
  by_cases hempty : σ.childPositions = []
  · have hruns0 : σ.numRuns = 0 := by
      have h := Ctx.numRuns_le_length σ
      rw [hempty] at h
      simp only [List.length_nil] at h
      omega
    have hτempty : τ.childPositions = [] := by
      by_cases hleft : σ.word.head? = some marker <;>
        by_cases hright : σ.word.getLast? = some marker <;>
        simp [τ, normalWord, hruns0, hleft, hright,
          Ctx.Context.childPositions, Ctx.Context.letterAt, marker] <;>
        intro p hp <;> interval_cases p <;> simp
    rw [hemptyBound σ hempty, hemptyBound τ hτempty]
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
  obtain ⟨b, hspan⟩ := hInterval σ hruns hempty
  have hN : 0 < σ.childPositions.length := List.length_pos_iff.mpr hempty
  have hmemChild (x : ℕ) : x ∈ σ.childPositions ↔
      b ≤ x ∧ x < b + σ.childPositions.length := by
    rw [hspan]
    simpa only [List.length_range'] using (List.mem_range'_1 (m := x) (s := b) (n := σ.childPositions.length))
  have hb : b ∈ σ.childPositions := (hmemChild b).mpr ⟨le_rfl, by omega⟩
  have hbRange : b < σ.word.length := List.mem_range.mp (List.mem_filter.mp hb).1
  have hbLetter : σ.letterAt b = Ctx.Letter.child :=
    of_decide_eq_true (List.mem_filter.mp hb).2
  have hfirst : σ.childPositions.head? = some b := by
    rw [hspan, List.head?_range']
    simp [ne_of_gt hN]
  have hprev : b = 0 ∨ σ.letterAt (b - 1) ≠ Ctx.Letter.child := by
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      intro he
      have hp : b - 1 ∈ σ.childPositions := by
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa using he⟩
      have := (hmemChild (b - 1)).mp hp
      omega
  have hstart : b ∈ ((List.range σ.word.length).filter fun p =>
      σ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)) := by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hbRange, hbLetter, hprev⟩
  have hruns1 : σ.numRuns = 1 := by
    have hh : 0 < σ.numRuns := List.length_pos_iff.mpr (List.ne_nil_of_mem hstart)
    omega
  have hlen : 0 < σ.word.length := by omega
  have hlastRange : σ.word.length - 1 < σ.word.length := by omega
  have hAt (x : ℕ) (hx : x < σ.word.length) :
      σ.letterAt x = Ctx.Letter.child ∨ σ.letterAt x = marker := by
    have hw := hletters _ (List.getElem_mem hx)
    simpa [Ctx.Context.letterAt, List.getElem?_eq_getElem hx, marker] using hw
  have hExtMem (x : ℕ) :
      x ∈ σ.extPositions 1 ↔ x < σ.word.length ∧ σ.letterAt x = marker := by
    constructor
    · intro hx
      have hxr : x < σ.word.length := List.mem_range.mp (List.mem_filter.mp hx).1
      rcases hAt x hxr with hc | hm
      · simp [Ctx.Context.extPositions, hc] at hx
      · exact ⟨hxr, hm⟩
    · rintro ⟨hxr, hm⟩
      simp [Ctx.Context.extPositions, hxr, hm, marker]
  have hheadAt : σ.word.head? = some marker ↔ σ.letterAt 0 = marker := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]
    simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hlen]
  have hlastAt : σ.word.getLast? = some marker ↔
      σ.letterAt (σ.word.length - 1) = marker := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlastRange]
    simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hlastRange]
  have hleft : ((σ.extPositions 1).filter (· < b)) ≠ [] ↔
      σ.word.head? = some marker := by
    constructor
    · intro hn
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
      have hxb : x < b := of_decide_eq_true (List.mem_filter.mp hx).2
      apply hheadAt.mpr
      rcases hAt 0 hlen with hc | hm
      · have hzeroChild : 0 ∈ σ.childPositions :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hlen, by simpa using hc⟩
        have := (hmemChild 0).mp hzeroChild
        omega
      · exact hm
    · intro hh
      have hzero := hheadAt.mp hh
      have hb0 : b ≠ 0 := by
        intro h
        subst b
        rw [hbLetter] at hzero
        exact hmarker hzero
      have hm : 0 ∈ (σ.extPositions 1).filter (· < b) :=
        List.mem_filter.mpr ⟨(hExtMem 0).mpr ⟨hlen, hzero⟩,
          by simpa using Nat.pos_of_ne_zero hb0⟩
      exact List.ne_nil_of_mem hm
  have hright : ((σ.extPositions 1).filter (b < ·)) ≠ [] ↔
      σ.word.getLast? = some marker := by
    constructor
    · intro hn
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
      have hbx : b < x := of_decide_eq_true (List.mem_filter.mp hx).2
      have hxm := (hExtMem x).mp (List.mem_filter.mp hx).1
      have houtside : b + σ.childPositions.length ≤ x := by
        by_contra h
        have hxc := (hmemChild x).mpr ⟨by omega, by omega⟩
        have hc := of_decide_eq_true (List.mem_filter.mp hxc).2
        rw [hc] at hxm
        exact hmarker hxm.2
      apply hlastAt.mpr
      rcases hAt (σ.word.length - 1) hlastRange with hc | hm
      · have hlastChild : σ.word.length - 1 ∈ σ.childPositions :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hlastRange, by simpa using hc⟩
        have := (hmemChild (σ.word.length - 1)).mp hlastChild
        omega
      · exact hm
    · intro hh
      have hlast := hlastAt.mp hh
      have hne : σ.word.length - 1 ≠ b := by
        intro h
        rw [h, hbLetter] at hlast
        exact hmarker hlast
      have hbl : b < σ.word.length - 1 := by omega
      have hm : σ.word.length - 1 ∈ (σ.extPositions 1).filter (b < ·) :=
        List.mem_filter.mpr ⟨(hExtMem _).mpr ⟨hlastRange, hlast⟩, by simpa using hbl⟩
      exact List.ne_nil_of_mem hm
  let q := if σ.word.head? = some marker then 1 else 0
  have hτchildren : τ.childPositions = [q] := by
    by_cases hL : σ.word.head? = some marker <;>
      by_cases hR : σ.word.getLast? = some marker <;>
      simp [τ, normalWord, hruns1, q, hL, hR, marker,
        Ctx.Context.childPositions, Ctx.Context.letterAt, List.range_succ]
  have hτleft : ((τ.extPositions 1).filter (· < q)) ≠ [] ↔
      σ.word.head? = some marker := by
    by_cases hL : σ.word.head? = some marker <;>
      by_cases hR : σ.word.getLast? = some marker <;>
      simp [τ, normalWord, hruns1, q, hL, hR, marker,
        Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
  have hτright : ((τ.extPositions 1).filter (q < ·)) ≠ [] ↔
      σ.word.getLast? = some marker := by
    by_cases hL : σ.word.head? = some marker <;>
      by_cases hR : σ.word.getLast? = some marker <;>
      simp [τ, normalWord, hruns1, q, hL, hR, marker,
        Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
  have hsideActual (hn : σ.extPositions 1 ≠ []) : σ.sideAt 1 = side := by
    obtain ⟨x, xs, he⟩ := List.exists_cons_of_ne_nil hn
    have hx : x ∈ σ.extPositions 1 := by rw [he]; simp
    have hm := (hExtMem x).mp hx
    simp [Ctx.Context.sideAt, he, hm.2, marker]
  have hrootSide : σ.sideAt 1 =
      if σ.word.head? = some marker ∨ σ.word.getLast? = some marker then side
      else Ctx.Side.lower := by
    by_cases he : σ.word.head? = some marker ∨ σ.word.getLast? = some marker
    · rw [if_pos he]
      apply hsideActual
      intro hn
      rcases he with hL | hR
      · have h := hleft.mpr hL
        simp [hn] at h
      · have h := hright.mpr hR
        simp [hn] at h
    · rw [if_neg he]
      have hn : σ.extPositions 1 = [] := by
        by_contra hn
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
        have hm := (hExtMem x).mp hx
        have hne : x ≠ b := by
          intro h
          rw [h, hbLetter] at hm
          exact hmarker hm.2
        by_cases hxb : x < b
        · exact he (Or.inl (hleft.mp (List.ne_nil_of_mem
            (List.mem_filter.mpr ⟨hx, by simpa using hxb⟩))))
        · have hbx : b < x := by omega
          exact he (Or.inr (hright.mp (List.ne_nil_of_mem
            (List.mem_filter.mpr ⟨hx, by simpa using hbx⟩))))
      simp [Ctx.Context.sideAt, hn]
  have hsideEq : σ.sideAt 1 = τ.sideAt 1 := by
    rw [hrootSide]
    by_cases hL : σ.word.head? = some marker <;>
      by_cases hR : σ.word.getLast? = some marker <;>
      simp [τ, normalWord, hruns1, hL, hR, marker,
        Ctx.Context.sideAt, Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
  have hτmax : τ.maxima = [m] := hmax
  have hLeftCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
      ρ.leftExt v 0 p =
        if ρ.sideAt 1 = v ∧ ((ρ.extPositions 1).filter (· < p)) ≠ [] then 1 else 0 := by
    by_cases hs : ρ.sideAt 1 = v
    · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      by_cases hn : ((ρ.extPositions 1).filter (· < p)) = []
      · simp [Ctx.Context.leftExt, hon, hn, hs, -List.getLast?_filter]
      · simp [Ctx.Context.leftExt, hon,
          List.getLast?_eq_some_getLast hn, hs, hn, -List.getLast?_filter,
          -List.getLast_filter]
    · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      simp [Ctx.Context.leftExt, hon, hs]
  have hRightCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
      ρ.rightExt v 0 p =
        if ρ.sideAt 1 = v ∧ ((ρ.extPositions 1).filter (p < ·)) ≠ [] then 1 else 0 := by
    by_cases hs : ρ.sideAt 1 = v
    · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      by_cases hn : ((ρ.extPositions 1).filter (p < ·)) = []
      · simp [Ctx.Context.rightExt, hon, hn, hs, -List.head?_filter]
      · simp [Ctx.Context.rightExt, hon,
          List.head?_eq_some_head hn, hs, hn, -List.head?_filter,
          -List.head_filter]
    · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      simp [Ctx.Context.rightExt, hon, hs]
  have hleftEq (v : Ctx.Side) : σ.leftExt v 0 b = τ.leftExt v 0 q := by
    simp only [hLeftCount σ b v hmax, hLeftCount τ q v hτmax, hsideEq, hleft, hτleft]
  have hrightEq (v : Ctx.Side) : σ.rightExt v 0 b = τ.rightExt v 0 q := by
    simp only [hRightCount σ b v hmax, hRightCount τ q v hτmax, hsideEq, hright, hτright]
  have hchainEq (v : Ctx.Side) : σ.chainExt v b b = τ.chainExt v q q := by
    simp only [Ctx.Context.chainExt, hleftEq, hrightEq]
  have hJoinCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
      ρ.joinExt v p p = max (ρ.chainExt v p p) (if ρ.sideAt 1 = v then m else 0) := by
    by_cases hs : ρ.sideAt 1 = v
    · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      simp [Ctx.Context.joinExt, hon, Ctx.Context.leftExt_one,
        Ctx.Context.rightExt_one, Ctx.Context.maximumAt, hm, hs]
    · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
      simp [Ctx.Context.joinExt, hon, hs]
  have hjoinEq (v : Ctx.Side) : σ.joinExt v b b = τ.joinExt v q q := by
    rw [hJoinCount σ b v hmax, hJoinCount τ q v hτmax, hchainEq, hsideEq]
  have hcup : σ.cupLimit b b = τ.cupLimit q q := by
    simp only [Ctx.Context.cupLimit, hchainEq, hjoinEq]
    all_goals rfl
  have hcap : σ.capLimit b b = τ.capLimit q q := by
    simp only [Ctx.Context.capLimit, hchainEq, hjoinEq]
    all_goals rfl
  have hbase (ρ : Ctx.Context) (p : ℕ) (hh : ρ.childPositions.head? = some p)
      (hr : ρ.numRuns ≤ 1) :
      ρ.bound = Ctx.Context.baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k := by
    unfold Ctx.Context.bound
    rw [Ctx.Context.boundFuel.eq_2, if_pos hr, Ctx.Context.base_eq_baseOf, hh]
    all_goals rfl
  have hτfirst : τ.childPositions.head? = some q := by rw [hτchildren]; rfl
  have hτruns : τ.numRuns ≤ 1 := by
    have h := Ctx.numRuns_le_length τ
    simpa [hτchildren] using h
  rw [hbase σ b hfirst hruns, hbase τ q hτfirst hτruns, hcup, hcap]

end ErdosSzekeres
