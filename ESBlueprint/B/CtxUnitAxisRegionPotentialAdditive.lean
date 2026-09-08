import ESBlueprint.B.CtxPartCapacityDropInClearInterval

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The active-region potential of a unit-axis context is additive across disjoint kept sets: a part on the chosen axis and a part on either axis have total potential at most the parent. Supports arbitrary maxima, empty parts, and sets that do not cover all children; positive external labels suffice. Exposes the local split invariant from the existing unit-axis bound proof so it can be combined with an opposite-axis chain-rank budget in the global-parameter-three argument.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_unit_axis_region_potential_additive (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (s : Ctx.Side)
  (hunit : ∀ p ∈ σ.childPositions,
    (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) ≤ 1)
  (keep rest : List ℕ) (t : Ctx.Side) (m n : ℕ)
  (hdis : ∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) :
  let regions := fun (ρ : Ctx.Context) =>
    let markers : Finset ℕ := (ρ.levelsOn s 0).toFinset.biUnion
      (fun l => (ρ.extPositions l).toFinset)
    let active : Finset ℕ := ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    (active.image (fun p => (markers.filter (· < p)).card)).card
  regions (σ.part keep s m) + regions (σ.part rest t n) ≤ regions σ := by
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
  have hClear (ρ : Context) (p q : ℕ) (hp : p ∈ ρ.childPositions)
      (hq : q ∈ ρ.childPositions) (he : label (marks ρ) p = label (marks ρ) q) :
      ∀ l ∈ ρ.levelsOn s 0, ∀ x ∈ ρ.extPositions l,
        x < min p q ∨ max p q < x := by
    intro l hl x hx
    exact (hLabelClear _ _ _ (hNoMark ρ p hp) (hNoMark ρ q hq)).mp he x
      ((hMark ρ x).mpr ⟨l, hl, hx⟩)
  have hPartActive (ρ : Context) (keep : List ℕ) (t : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep t m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    simp only [decide_eq_true_eq] at hk
    have hle := ctx_part_limits_le ρ keep t m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, hk⟩
  have hPartMarks (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (keep : List ℕ) (t : Side) (m x : ℕ) (hx : x ∈ marks (ρ.part keep t m)) :
      x ∈ marks ρ ∨ (t = s ∧ x ∈ ρ.childPositions ∧ x ∉ keep) := by
    obtain ⟨l, hl, hx⟩ := (hMark _ _).mp hx
    have hl' := List.mem_filter.mp hl
    have hs : (ρ.part keep t m).sideAt l = s := by simpa using hl'.2
    rw [part_levels] at hl'
    rcases List.mem_cons.mp hl'.1 with rfl | hold
    · right
      have hside := part_sideAt_one_of_mem hPos keep t m hx
      rw [part_extPositions_one hPos keep t m] at hx
      have hr := List.mem_filter.mp hx
      exact ⟨hside.symm.trans hs, hr.1, by simpa using hr.2⟩
    · left
      obtain ⟨j, hj, hjl⟩ := List.mem_map.mp hold
      subst l
      have h1 := one_le_of_mem_levels hj
      rw [part_extPositions_succ ρ keep t m h1] at hx
      rw [part_sideAt_succ ρ keep t m h1] at hs
      exact (hMark ρ x).mpr ⟨j, by simp [Context.levelsOn, hj, hs], hx⟩
  have hExclude (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep : List ℕ) (m p r : ℕ) (hp : p ∈ active (ρ.part keep s m))
      (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep)
      (hclear : ∀ l ∈ ρ.levelsOn s 0, ∀ x ∈ ρ.extPositions l,
        x < min p r ∨ max p r < x) : False := by
    have hpa := hPartActive ρ keep s m p hp
    have hpc := ((hActive ρ p).mp hpa.1).1
    have hd := (ctx_part_capacity_drop_in_clear_interval ρ hPos keep s m p r
      hpc hpa.2 hr hremoved hclear).2.2
    have hu := hUnit p hpc
    have hpp := (hActive _ _).mp hp
    cases s <;> dsimp [lim] at hu hd <;> omega
  have hPartLabels (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep : List ℕ) (t : Side) (m p q : ℕ)
      (hp : p ∈ active (ρ.part keep t m)) (hq : q ∈ active (ρ.part keep t m))
      (he : label (marks ρ) p = label (marks ρ) q) :
      label (marks (ρ.part keep t m)) p = label (marks (ρ.part keep t m)) q := by
    have hpc := ((hActive _ _).mp (hPartActive ρ keep t m p hp).1).1
    have hqc := ((hActive _ _).mp (hPartActive ρ keep t m q hq).1).1
    have hc := hClear ρ p q hpc hqc he
    apply (hLabelClear _ _ _
      (hNoMark _ _ ((hActive _ _).mp hp).1)
      (hNoMark _ _ ((hActive _ _).mp hq).1)).mpr
    intro x hx
    rcases hPartMarks ρ hPos keep t m x hx with hold | ⟨ht, hxchild, hxremoved⟩
    · obtain ⟨l, hl, hx⟩ := (hMark ρ x).mp hold
      exact hc l hl x hx
    · by_contra hout
      subst t
      apply hExclude ρ hPos hUnit keep m p x hp hxchild hxremoved
      intro l hl y hy
      have := hc l hl y hy
      omega
  have hImageCard : ∀ (A : Finset ℕ) (f g : ℕ → ℕ),
      (∀ p ∈ A, ∀ q ∈ A, g p = g q → f p = f q) →
      (A.image f).card ≤ (A.image g).card := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro f g _; simp
    | @insert p A hp ih =>
      intro f g hfg
      have hsmall := ih f g (fun x hx y hy he => hfg x (by simp [hx]) y (by simp [hy]) he)
      rw [Finset.image_insert, Finset.image_insert]
      by_cases hg : g p ∈ A.image g
      · obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hg
        have hf : f p ∈ A.image f := Finset.mem_image.mpr
          ⟨q, hq, (hfg p (by simp) q (by simp [hq]) heq.symm).symm⟩
        simpa only [Finset.insert_eq_of_mem hg, Finset.insert_eq_of_mem hf] using hsmall
      · rw [Finset.card_insert_of_notMem hg]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hsmall 1)
  have hCut (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1)
      (keep rest : List ℕ) (t : Side) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      ν (ρ.part keep s m) + ν (ρ.part rest t n) ≤ ν ρ := by
    let A := active (ρ.part keep s m)
    let B := active (ρ.part rest t n)
    let f := label (marks ρ)
    have hA : ν (ρ.part keep s m) ≤ (A.image f).card :=
      hImageCard A _ _ (fun p hp q hq he => hPartLabels ρ hPos hUnit keep s m p q hp hq he)
    have hB : ν (ρ.part rest t n) ≤ (B.image f).card :=
      hImageCard B _ _ (fun p hp q hq he => hPartLabels ρ hPos hUnit rest t n p q hp hq he)
    have hAB : Disjoint (A.image f) (B.image f) := by
      apply Finset.disjoint_left.mpr
      intro v hvA hvB
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hvA
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hvB
      have hpa := hPartActive ρ keep s m p hp
      have hqa := hPartActive ρ rest t n q hq
      have hpc := ((hActive _ _).mp hpa.1).1
      have hqc := ((hActive _ _).mp hqa.1).1
      have hnot : q ∉ keep := fun hk => hdis q hqc hk hqa.2
      exact hExclude ρ hPos hUnit keep m p q hp hqc hnot
        (hClear ρ p q hpc hqc hqp.symm)
    have hsub : A.image f ∪ B.image f ⊆ (active ρ).image f := by
      intro v hv
      rcases Finset.mem_union.mp hv with ha | hb
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ keep s m p hp).1, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ rest t n p hp).1, rfl⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hAB] at hcard
    exact (Nat.add_le_add hA hB).trans hcard
  exact hCut σ hpositive hunit keep rest t m n hdis

end ErdosSzekeres
