import ESBlueprint.B.CtxUnitAxisRegionPotentialAdditive

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A unit-capacity context is bounded by its active regions, separated only by indexed external positions on the chosen side. Every fuel approximation and the full bound are at most that region count, which is at most the physical child-run count. Exposes the stronger invariant underlying the unit-axis run theorem; opposite-side gaps can merge several physical runs into one region. Positive external labels suffice. The proof gives additive decrease for arbitrary disjoint kept sets and arbitrary new maxima.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_le_numRuns_of_unit_axis_limit -/
theorem ctx_unit_axis_active_region_potential (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (s : Ctx.Side)
  (hunit : ∀ p ∈ σ.childPositions,
    (match s with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) ≤ 1) :
  let markers : Finset ℕ := (σ.levelsOn s 0).toFinset.biUnion
    (fun l => (σ.extPositions l).toFinset)
  let active : Finset ℕ := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let regions := (active.image (fun p => (markers.filter (· < p)).card)).card
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ regions) ∧
    σ.bound ≤ regions ∧ regions ≤ σ.numRuns := by
  classical
  dsimp only
  let lim (ρ : Context) (p : ℕ) := match s with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun l => (ρ.extPositions l).toFinset)
  let label (M : Finset ℕ) (p : ℕ) := (M.filter (· < p)).card
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ν (ρ : Context) := ((active ρ).image (label (marks ρ))).card
  have hMark (ρ : Context) (x : ℕ) :
      x ∈ marks ρ ↔ ∃ l ∈ ρ.levelsOn s 0, x ∈ ρ.extPositions l := by
    simp [marks]
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hNoMark (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) : p ∉ marks ρ := by
    intro hm
    obtain ⟨l, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
  have hLabelClear (M : Finset ℕ) (p q : ℕ) (hp : p ∉ M) (hq : q ∉ M) :
      label M p = label M q ↔ ∀ x ∈ M, x < min p q ∨ max p q < x := by
    have hordered (a b : ℕ) (hab : a ≤ b) (hb : b ∉ M)
        (he : label M a = label M b) : ∀ x ∈ M, x < a ∨ b < x := by
      have hs : M.filter (· < a) ⊆ M.filter (· < b) := by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by omega⟩
      have hf := Finset.eq_of_subset_of_card_le hs (show label M b ≤ label M a by omega)
      intro x hx
      by_cases hxa : x < a
      · exact Or.inl hxa
      · right
        by_contra hbx
        have hneq : x ≠ b := by intro h; subst x; exact hb hx
        have hxb : x < b := by omega
        have hx' : x ∈ M.filter (· < a) := by rw [hf]; exact Finset.mem_filter.mpr ⟨hx, hxb⟩
        exact hxa (Finset.mem_filter.mp hx').2
    constructor
    · intro he
      rcases le_total p q with hpq | hqp
      · simpa only [min_eq_left hpq, max_eq_right hpq] using hordered p q hpq hq he
      · simpa only [min_eq_right hqp, max_eq_left hqp] using hordered q p hqp hp he.symm
    · intro hc
      apply congrArg Finset.card
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter]
      constructor <;> intro hx
      · exact ⟨hx.1, by have := hc x hx.1; omega⟩
      · exact ⟨hx.1, by have := hc x hx.1; omega⟩
  have hCut (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep rest : List ℕ) (t : Side) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      ν (ρ.part keep s m) + ν (ρ.part rest t n) ≤ ν ρ := by
    exact ctx_unit_axis_region_potential_additive ρ hPos s hUnit keep rest t m n hdis
  have hCutLR (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      ν (ρ.part keep Side.lower m) + ν (ρ.part rest Side.upper n) ≤ ν ρ := by
    cases hs : s with
    | lower => simpa only [hs] using hCut ρ hPos hUnit keep rest Side.upper m n hdis
    | upper =>
      have hrev : ∀ p ∈ ρ.childPositions, p ∈ rest → p ∉ keep := by
        intro p hp hr hk
        exact hdis p hp hk hr
      simpa only [hs, Nat.add_comm] using hCut ρ hPos hUnit rest keep Side.lower n m hrev
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x l u, (ρ.part keep t m).letterAt x = Letter.ext l u → 1 ≤ l := by
    intro x l u hx
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
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx
      omega
  have hUnitPart (ρ : Context) (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ p ∈ (ρ.part keep t m).childPositions, lim (ρ.part keep t m) p ≤ 1 := by
    intro p hp
    rw [part_childPositions] at hp
    have hu := hUnit p (List.mem_filter.mp hp).1
    have hle := ctx_part_limits_le ρ keep t m p p
    cases s <;> dsimp [lim] at hu ⊢ <;> omega
  have hBase (ρ : Context) (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1) : ρ.base ≤ ν ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have hu := hUnit p hp
      have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
        cases s <;> dsimp [lim] at hu <;> omega
      have ha : p ∈ active ρ := (hActive _ _).mpr ⟨hp, hpos⟩
      have hn : ((active ρ).image (label (marks ρ))).Nonempty :=
        ⟨label (marks ρ) p, Finset.mem_image.mpr ⟨p, ha, rfl⟩⟩
      simpa only [baseOf, if_neg hz, if_pos hone] using Finset.card_pos.mpr hn
  have hFuel : ∀ fuel (ρ : Context),
      (∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l) →
      (∀ p ∈ ρ.childPositions, lim ρ p ≤ 1) → boundFuel fuel ρ ≤ ν ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hUnit
      rw [boundFuel]
      split
      · exact hBase ρ hUnit
      · apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        have hparts (keep : List ℕ) (t : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep t m) ≤ ν (ρ.part keep t m) :=
          ih _ (hPositivePart ρ keep t m) (hUnitPart ρ hUnit keep t m)
        rcases hx with rfl | rfl
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          apply hCutLR ρ hPos hUnit
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          rw [Nat.add_comm]
          apply hCutLR ρ hPos hUnit
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  have hRuns (ρ : Context) : ν ρ ≤ ρ.numRuns := by
    let starts := (List.range ρ.word.length).filter (fun p =>
      ρ.letterAt p = Letter.child ∧ (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child))
    have hstart : ∀ p, p ∈ ρ.childPositions →
        ∃ r ∈ starts, label (marks ρ) r = label (marks ρ) p := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hp
        have hc : p < ρ.word.length ∧ ρ.letterAt p = Letter.child := by
          simpa only [Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq] using hp
        by_cases hnew : p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child
        · exact ⟨p, by simp [starts, hc.1, hc.2, hnew], rfl⟩
        · have hpred : p - 1 ∈ ρ.childPositions := by
            simp only [Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq]
            exact ⟨by omega, by push Not at hnew; exact hnew.2⟩
          obtain ⟨r, hr, he⟩ := ih (p - 1) (by omega) hpred
          refine ⟨r, hr, he.trans ?_⟩
          apply (hLabelClear _ _ _ (hNoMark ρ (p - 1) hpred) (hNoMark ρ p hp)).mpr
          intro x hx
          have hx1 : x ≠ p - 1 := by intro h; subst x; exact hNoMark ρ _ hpred hx
          have hx2 : x ≠ p := by intro h; subst x; exact hNoMark ρ _ hp hx
          omega
    have hsub : (active ρ).image (label (marks ρ)) ⊆
        starts.toFinset.image (label (marks ρ)) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨r, hr, he⟩ := hstart p ((hActive _ _).mp hp).1
      exact Finset.mem_image.mpr ⟨r, List.mem_toFinset.mpr hr, he⟩
    calc
      ν ρ ≤ (starts.toFinset.image (label (marks ρ))).card := Finset.card_le_card hsub
      _ ≤ starts.toFinset.card := Finset.card_image_le
      _ = starts.length := List.toFinset_card_of_nodup (List.nodup_range.filter _)
      _ = ρ.numRuns := rfl
  exact ⟨fun fuel => hFuel fuel σ hpositive hunit,
    hFuel _ σ hpositive hunit, hRuns σ⟩

end ErdosSzekeres
