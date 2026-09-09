import ESBlueprint.B.CtxPartCapacityDropInClearInterval

import ESBlueprint.B.CtxActiveUnitAxisThreeZonePotential

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An occupied-color potential for a mixed-axis clear unit cover, with arbitrary global parameters. Each color chooses its own axis; source-active children of that color have chosen capacity at most one, and every pair has a clear interval on that axis. Positive labels suffice, with arbitrary inactive children and empty active support. The number of occupied colors bounds every fuel approximation and the full recursive bound and is additive across arbitrary disjoint lower/upper parts with arbitrary new maxima. Part-active children inherit source activity and unit capacity; a new marker between same-color survivors would kill one by strict capacity drop, preserving clear intervals. A color shared by both sides of a cut is likewise impossible. Supplies a sharper mixed-axis certificate for the all-unit recursive-part gap in the singleton-end sandwich mixed potential, where a three-zone estimate overcounts an opposite-axis clear unit pair.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_mixed_axis_clear_unit_cover_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (color : ℕ → ℕ) (axis : ℕ → Ctx.Side)
  (hunit : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match axis (color p) with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) ≤ 1)
  (hclear : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    0 < σ.cupLimit q q → 0 < σ.capLimit q q → color p = color q →
    ∀ j ∈ σ.levelsOn (axis (color p)) 0, ∀ x ∈ σ.extPositions j,
      x < min p q ∨ max p q < x) :
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let potential := fun (ρ : Ctx.Context) => ((active ρ).image color).card
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ potential σ) ∧ σ.bound ≤ potential σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      potential (σ.part keep Ctx.Side.lower m) +
        potential (σ.part rest Ctx.Side.upper n) ≤ potential σ) := by
  classical
  let C (ρ : Context) (v : Side) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let marks (ρ : Context) (v : Side) :=
    (ρ.levelsOn v 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let V (ρ : Context) := ((active ρ).image color).card
  let Good (ρ : Context) : Prop :=
    (∀ p ∈ active ρ, C ρ (axis (color p)) p ≤ 1) ∧
    (∀ p ∈ active ρ, ∀ q ∈ active ρ, color p = color q →
      ∀ j ∈ ρ.levelsOn (axis (color p)) 0, ∀ x ∈ ρ.extPositions j,
        x < min p q ∨ max p q < x)
  change (∀ fuel, boundFuel fuel σ ≤ V σ) ∧ σ.bound ≤ V σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      V (σ.part keep Side.lower m) + V (σ.part rest Side.upper n) ≤ V σ)
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
  have hMark (ρ : Context) (v : Side) (x : ℕ) :
      x ∈ marks ρ v ↔ ∃ j ∈ ρ.levelsOn v 0, x ∈ ρ.extPositions j := by simp [marks]
  have hPartActive (ρ : Context) (keep : List ℕ) (v : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    simp only [decide_eq_true_eq] at hk
    have hle := ctx_part_limits_le ρ keep v m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, hk⟩
  have hPartMarks (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (w v : Side) (m x : ℕ) (hx : x ∈ marks (ρ.part keep w m) v) :
      x ∈ marks ρ v ∨ (w = v ∧ x ∈ ρ.childPositions ∧ x ∉ keep) := by
    obtain ⟨j, hj, hx⟩ := (hMark _ _ _).mp hx
    have hj' := List.mem_filter.mp hj
    have hs : (ρ.part keep w m).sideAt j = v := by simpa using hj'.2
    rw [part_levels] at hj'
    rcases List.mem_cons.mp hj'.1 with rfl | hold
    · right
      have hside := part_sideAt_one_of_mem hPos keep w m hx
      rw [part_extPositions_one hPos keep w m] at hx
      have hr := List.mem_filter.mp hx
      exact ⟨hside.symm.trans hs, hr.1, by simpa using hr.2⟩
    · left
      obtain ⟨i, hi, hij⟩ := List.mem_map.mp hold
      subst j
      have hi1 := one_le_of_mem_levels hi
      rw [part_extPositions_succ ρ keep w m hi1] at hx
      rw [part_sideAt_succ ρ keep w m hi1] at hs
      exact (hMark ρ v x).mpr ⟨i, by simp [Context.levelsOn, hi, hs], hx⟩
  have hExclude (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep)
      (hUnit : C ρ v p ≤ 1)
      (hClear : ∀ j ∈ ρ.levelsOn v 0, ∀ x ∈ ρ.extPositions j,
        x < min p q ∨ max p q < x) : False := by
    have hpa := hPartActive ρ keep v m p hp
    have hpc := ((hActive ρ p).mp hpa.1).1
    have hd := (ctx_part_capacity_drop_in_clear_interval ρ hPos keep v m p q
      hpc hpa.2 hq hnot hClear).2.2
    have hpp := (hActive _ _).mp hp
    cases v <;> dsimp only [C] at hUnit hd <;> omega
  have hGoodPart (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hg : Good ρ) (keep : List ℕ) (w : Side) (m : ℕ) : Good (ρ.part keep w m) := by
    constructor
    · intro p hp
      have hpa := hPartActive ρ keep w m p hp
      have hu := hg.1 p hpa.1
      have hle := ctx_part_limits_le ρ keep w m p p
      cases hv : axis (color p) <;> simp only [hv, C] at hu ⊢ <;> omega
    · intro p hp q hq he j hj x hx
      have hpa := hPartActive ρ keep w m p hp
      have hqa := hPartActive ρ keep w m q hq
      have hc := hg.2 p hpa.1 q hqa.1 he
      have hxm : x ∈ marks (ρ.part keep w m) (axis (color p)) :=
        (hMark _ _ _).mpr ⟨j, hj, hx⟩
      rcases hPartMarks ρ hPos keep w (axis (color p)) m x hxm with hold | ⟨hw, hxc, hxn⟩
      · obtain ⟨i, hi, hxi⟩ := (hMark _ _ _).mp hold
        exact hc i hi x hxi
      · by_contra hout
        apply hExclude ρ hPos keep w m p x hp hxc hxn
        · rw [hw]
          exact hg.1 p hpa.1
        · intro i hi y hy
          rw [hw] at hi
          have hh := hc i hi y hy
          omega
  have hCut (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hg : Good ρ) (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      V (ρ.part keep Side.lower m) + V (ρ.part rest Side.upper n) ≤ V ρ := by
    let A := active (ρ.part keep Side.lower m)
    let B := active (ρ.part rest Side.upper n)
    have hab : Disjoint (A.image color) (B.image color) := by
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzA
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hzB
      have hpa := hPartActive ρ keep Side.lower m p hp
      have hqa := hPartActive ρ rest Side.upper n q hq
      have hpc := ((hActive _ _).mp hpa.1).1
      have hqc := ((hActive _ _).mp hqa.1).1
      have hqnot : q ∉ keep := fun hk => hdis q hqc hk hqa.2
      have hpnot : p ∉ rest := hdis p hpc hpa.2
      cases hv : axis (color p) with
      | lower =>
        apply hExclude ρ hPos keep Side.lower m p q hp hqc hqnot
        · rw [← hv]
          exact hg.1 p hpa.1
        · simpa only [hv] using hg.2 p hpa.1 q hqa.1 hqp.symm
      | upper =>
        have hvq : axis (color q) = Side.upper := by rw [hqp]; exact hv
        apply hExclude ρ hPos rest Side.upper n q p hq hpc hpnot
        · rw [← hvq]
          exact hg.1 q hqa.1
        · simpa only [hvq] using hg.2 q hqa.1 p hpa.1 hqp
    have hsub : A.image color ∪ B.image color ⊆ (active ρ).image color := by
      intro z hz
      rcases Finset.mem_union.mp hz with ha | hb
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ keep Side.lower m p hp).1, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨q, (hPartActive ρ rest Side.upper n q hq).1, rfl⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hab] at hh
    exact hh
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x j v, (ρ.part keep t m).letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx; omega
  have hBase (ρ : Context) (hg : Good ρ) : ρ.base ≤ V ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ V ρ
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpa : p ∈ active ρ := (hActive _ _).mpr ⟨hp, by omega, by omega⟩
      have hu := hg.1 p hpa
      have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
        cases hv : axis (color p) <;> simp only [hv, C] at hu <;> omega
      have hn : ((active ρ).image color).Nonempty := ⟨color p, Finset.mem_image.mpr ⟨p, hpa, rfl⟩⟩
      simpa only [baseOf, if_neg hz, if_pos hone] using Finset.card_pos.mpr hn
  have hFuel : ∀ fuel (ρ : Context),
      (∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j) → Good ρ → boundFuel fuel ρ ≤ V ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg
      rw [boundFuel]
      split
      · exact hBase ρ hg
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, _, d, _, hz⟩ := hz
        have hparts (ks : List ℕ) (v : Side) (c : ℕ) :
            boundFuel fuel (ρ.part ks v c) ≤ V (ρ.part ks v c) :=
          ih _ (hPositivePart ρ ks v c) (hGoodPart ρ hPos hg ks v c)
        rcases hz with rfl | rfl
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          apply hCut ρ hPos hg
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          rw [Nat.add_comm]
          apply hCut ρ hPos hg
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  have hOurGood : Good σ := by
    constructor
    · intro p hp
      obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
      exact hunit p hc hcup hcap
    · intro p hp q hq he
      obtain ⟨hpc, hpcup, hpcap⟩ := (hActive _ _).mp hp
      obtain ⟨hqc, hqcup, hqcap⟩ := (hActive _ _).mp hq
      exact hclear p hpc q hqc hpcup hpcap hqcup hqcap he
  exact ⟨fun fuel => hFuel fuel σ hpositive hOurGood, hFuel _ σ hpositive hOurGood,
    fun keep rest m n hdis => hCut σ hpositive hOurGood keep rest m n hdis⟩

end ErdosSzekeres
