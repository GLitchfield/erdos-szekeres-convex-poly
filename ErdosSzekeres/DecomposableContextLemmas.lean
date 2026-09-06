module

public import ErdosSzekeres.DecomposableContext

@[expose] public section

/-!
# Lemmas about contexts (Workstream B)

Proved helpers for the context induction of experiments 0117 to 0122: list maxima,
monotonicity of `decomposableThreshold`, the `Dominates` relation and antitonicity of the
recursion, letters and sides of a part, the level-one maximum, chain maxima, and the
positions of a subset.  Moved here from the B node modules so that several nodes can
share them (the core does not import ESBlueprint).
-/

namespace ErdosSzekeres


/-! ### Monotonicity of the threshold in its first two parameters -/

/-- Row `k-1` of Pascal's triangle is dominated by any window of row `k-2` that contains
the two entries `k-a` and `k-a+1`. -/
theorem choose_le_sum_choose_window {a k lo hi : ℕ} (ha : 2 ≤ a) (hak : a ≤ k + 1) (hk : 2 ≤ k)
    (hlo : lo ≤ k - a) (hhi : k - a + 1 ≤ hi) :
    Nat.choose (k - 1) (a - 2) ≤ ∑ j ∈ Finset.Icc lo hi, Nat.choose (k - 2) j := by
  have hsub : ({k - a, k - a + 1} : Finset ℕ) ⊆ Finset.Icc lo hi := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hpair : Nat.choose (k - 1) (a - 2) ≤ Nat.choose (k - 2) (k - a) + Nat.choose (k - 2) (k - a + 1) := by
    rcases (lt_or_eq_of_le hak) with hlt | heq
    · have hsym : Nat.choose (k - 1) (a - 2) = Nat.choose (k - 1) (k - a + 1) := by
        rw [← Nat.choose_symm (by omega : a - 2 ≤ k - 1)]
        congr 1
        omega
      have hpas : Nat.choose (k - 1) (k - a + 1) =
          Nat.choose (k - 2) (k - a) + Nat.choose (k - 2) (k - a + 1) := by
        have e : k - 1 = (k - 2) + 1 := by omega
        rw [e, Nat.choose_succ_succ']
      rw [hsym, hpas]
    · subst heq
      have e1 : k + 1 - 2 = k - 1 := by omega
      have e2 : k - (k + 1) = 0 := by omega
      rw [e1, e2, Nat.choose_self, Nat.choose_zero_right]
      exact Nat.le_add_right _ _
  calc Nat.choose (k - 1) (a - 2)
      ≤ Nat.choose (k - 2) (k - a) + Nat.choose (k - 2) (k - a + 1) := hpair
    _ = ∑ j ∈ ({k - a, k - a + 1} : Finset ℕ), Nat.choose (k - 2) j := by
        rw [Finset.sum_pair (by omega)]
    _ ≤ ∑ j ∈ Finset.Icc lo hi, Nat.choose (k - 2) j := Finset.sum_le_sum_of_subset hsub

theorem decomposableThreshold_two_two (k : ℕ) : decomposableThreshold 2 2 k = 1 := by
  rcases k with _ | k
  · decide
  · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    simp

theorem decomposableThreshold_le_succ_left {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) :
    decomposableThreshold a u k ≤ decomposableThreshold (a + 1) u k := by
  rcases lt_or_ge (a + u) (k + 3) with hlt | hge
  · rw [decomposableThreshold_eq_choose ha hu hlt.le,
      decomposableThreshold_eq_choose (by omega) hu (by omega)]
    obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 2 := ⟨u - 2, by omega⟩
    rw [show i + 2 + (v + 2) - 4 = i + v by omega, show i + 2 + 1 + (v + 2) - 4 = i + v + 1 by omega,
      show i + 2 - 2 = i by omega, show i + 2 + 1 - 2 = i + 1 by omega, Nat.choose_succ_succ']
    exact Nat.le_add_right _ _
  · rcases lt_or_eq_of_le hge with hgt | heq
    · rw [decomposableThreshold_eq_window ha hu (by omega),
        decomposableThreshold_eq_window (by omega) hu (by omega)]
      unfold decomposableBinomialWindow
      exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
    · rcases lt_or_ge k 2 with hk | hk
      · have ha2 : a = 2 := by omega
        have hu2 : u = 2 := by omega
        have hk1 : k = 1 := by omega
        subst ha2 hu2 hk1
        decide
      · rcases lt_or_eq_of_le (show a ≤ k + 1 by omega) with hak | hak
        · rw [decomposableThreshold_eq_choose ha hu (by omega),
            decomposableThreshold_eq_window (by omega) hu (by omega)]
          unfold decomposableBinomialWindow
          rw [show a + u - 4 = k - 1 by omega]
          exact choose_le_sum_choose_window ha (by omega) hk (by omega) (by omega)
        · have hu2 : u = 2 := by omega
          subst hak hu2
          rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
            decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
          unfold decomposableBinomialWindow
          rw [show k + 1 + 2 - 4 = k - 1 by omega, show k + 1 - 2 = k - 1 by omega, Nat.choose_self,
            show k - (k + 1 + 1) = 0 by omega, show (2 : ℕ) - 2 = 0 by omega, Finset.Icc_self,
            Finset.sum_singleton, Nat.choose_zero_right]

theorem decomposableThreshold_le_succ_right {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) :
    decomposableThreshold a u k ≤ decomposableThreshold a (u + 1) k := by
  rcases lt_or_ge (a + u) (k + 3) with hlt | hge
  · rw [decomposableThreshold_eq_choose ha hu hlt.le,
      decomposableThreshold_eq_choose ha (by omega) (by omega)]
    rw [show a + (u + 1) - 4 = (a + u - 4) + 1 by omega]
    exact Nat.choose_le_succ _ _
  · rcases lt_or_eq_of_le hge with hgt | heq
    · rw [decomposableThreshold_eq_window ha hu (by omega),
        decomposableThreshold_eq_window ha (by omega) (by omega)]
      unfold decomposableBinomialWindow
      exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    · rcases lt_or_ge k 2 with hk | hk
      · have ha2 : a = 2 := by omega
        have hu2 : u = 2 := by omega
        have hk1 : k = 1 := by omega
        subst ha2 hu2 hk1
        decide
      · rw [decomposableThreshold_eq_choose ha hu (by omega),
          decomposableThreshold_eq_window ha (by omega) (by omega)]
        unfold decomposableBinomialWindow
        rw [show a + u - 4 = k - 1 by omega]
        exact choose_le_sum_choose_window ha (by omega) hk le_rfl (by omega)

/-- The threshold is monotone in each of its first two parameters from `2` on. -/
theorem decomposableThreshold_mono {a a' u u' k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u)
    (haa : a ≤ a') (huu : u ≤ u') :
    decomposableThreshold a u k ≤ decomposableThreshold a' u' k := by
  have h1 : decomposableThreshold a u k ≤ decomposableThreshold a' u k := by
    induction a', haa using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact ih.trans (decomposableThreshold_le_succ_left (by omega) hu)
  have h2 : decomposableThreshold a' u k ≤ decomposableThreshold a' u' k := by
    induction u', huu using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact ih.trans (decomposableThreshold_le_succ_right (by omega) (by omega))
  exact h1.trans h2

theorem one_le_decomposableThreshold {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) :
    1 ≤ decomposableThreshold a u k := by
  have := decomposableThreshold_mono (a := 2) (u := 2) (a' := a) (u' := u) (k := k) le_rfl le_rfl ha hu
  rwa [decomposableThreshold_two_two] at this

namespace Ctx

/-! ### Maxima of lists -/

theorem mem_le_foldl_max (z : ℕ) (zs : List ℕ) : ∀ {y : ℕ}, y ∈ z :: zs → y ≤ zs.foldl max z := by
  induction zs generalizing z with
  | nil => intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; simp [hy]
  | cons w ws ih =>
    intro y hy
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact (le_max_left y w).trans (ih (max y w) (List.mem_cons_self ..))
    · exact (le_max_right z y).trans (ih (max z y) (List.mem_cons_self ..))
    · exact ih (max z w) (List.mem_cons.2 (Or.inr hy))

theorem foldl_max_le (b : ℕ) (zs : List ℕ) : ∀ (z : ℕ), z ≤ b → (∀ y ∈ zs, y ≤ b) → zs.foldl max z ≤ b := by
  induction zs with
  | nil => intro z hz _; simpa using hz
  | cons w ws ih =>
    intro z hz hws
    simp only [List.foldl_cons]
    exact ih (max z w) (max_le hz (hws w (List.mem_cons_self ..))) fun y hy => hws y (List.mem_cons.2 (Or.inr hy))

/-- A list whose members are each dominated by a member of another list has a smaller
maximum (with `0` for the empty list). -/
theorem getD_max?_le_of_forall (L₁ L₂ : List ℕ) (hL : ∀ x ∈ L₁, ∃ y ∈ L₂, x ≤ y) :
    (L₁.max?).getD 0 ≤ (L₂.max?).getD 0 := by
  cases L₁ with
  | nil => simp
  | cons x xs =>
    cases L₂ with
    | nil =>
      obtain ⟨y, hy, _⟩ := hL x (List.mem_cons_self ..)
      simp at hy
    | cons z zs =>
      simp only [List.max?_cons', Option.getD_some]
      apply foldl_max_le
      · obtain ⟨y, hy, hxy⟩ := hL x (List.mem_cons_self ..)
        exact hxy.trans (mem_le_foldl_max z zs hy)
      · intro w hw
        obtain ⟨y, hy, hwy⟩ := hL w (List.mem_cons.2 (Or.inr hw))
        exact hwy.trans (mem_le_foldl_max z zs hy)

theorem getD_max?_map_le {α : Type*} (L : List α) (f g : α → ℕ) (hfg : ∀ x ∈ L, f x ≤ g x) :
    ((L.map f).max?).getD 0 ≤ ((L.map g).max?).getD 0 := by
  apply getD_max?_le_of_forall
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact ⟨g a, List.mem_map.2 ⟨a, ha, rfl⟩, hfg a ha⟩

namespace Context

/-! ### Contexts with pointwise dominated sibling maxima -/

/-- Same parameters and word, the same number of levels, and pointwise larger sibling
maxima in `σ₂`. -/
structure Dominates (σ₁ σ₂ : Context) : Prop where
  a : σ₁.a = σ₂.a
  u : σ₁.u = σ₂.u
  k : σ₁.k = σ₂.k
  word : σ₁.word = σ₂.word
  length : σ₁.maxima.length = σ₂.maxima.length
  le : ∀ N, σ₁.maximumAt N ≤ σ₂.maximumAt N

/-- The base value as a function of the two limits and `k`. -/
def baseOf (cl pl k : ℕ) : ℕ :=
  if cl = 0 ∨ pl = 0 then 0
  else if cl = 1 ∨ pl = 1 then 1
  else decomposableThreshold (pl + 1) (cl + 1) k

theorem baseOf_mono {cl cl' pl pl' k : ℕ} (hc : cl ≤ cl') (hp : pl ≤ pl') :
    baseOf cl pl k ≤ baseOf cl' pl' k := by
  unfold baseOf
  by_cases h0 : cl = 0 ∨ pl = 0
  · rw [if_pos h0]
    exact Nat.zero_le _
  rw [if_neg h0]
  have h0' : ¬ (cl' = 0 ∨ pl' = 0) := by omega
  rw [if_neg h0']
  by_cases h1 : cl = 1 ∨ pl = 1
  · rw [if_pos h1]
    by_cases h1' : cl' = 1 ∨ pl' = 1
    · rw [if_pos h1']
    · rw [if_neg h1']
      exact one_le_decomposableThreshold (by omega) (by omega)
  rw [if_neg h1]
  have h1' : ¬ (cl' = 1 ∨ pl' = 1) := by omega
  rw [if_neg h1']
  exact decomposableThreshold_mono (by omega) (by omega) (by omega) (by omega)

theorem base_eq_baseOf (σ : Context) :
    σ.base = match σ.childPositions.head? with
      | none => 0
      | some p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k := rfl

namespace Dominates

variable {σ₁ σ₂ : Context} (h : Dominates σ₁ σ₂)
include h

theorem letterAt (p : ℕ) : σ₁.letterAt p = σ₂.letterAt p := by
  simp only [Context.letterAt, h.word]

theorem childPositions : σ₁.childPositions = σ₂.childPositions := by
  simp only [Context.childPositions, h.letterAt, h.word]

theorem extPositions (l : ℕ) : σ₁.extPositions l = σ₂.extPositions l := by
  simp only [Context.extPositions, h.letterAt, h.word]

theorem sideAt (l : ℕ) : σ₁.sideAt l = σ₂.sideAt l := by
  simp only [Context.sideAt, h.extPositions, h.letterAt]

theorem levels : σ₁.levels = σ₂.levels := by
  simp only [Context.levels, h.length]

theorem numRuns : σ₁.numRuns = σ₂.numRuns := by
  simp only [Context.numRuns, h.letterAt, h.word]

theorem levelsOn (s : Side) (top : ℕ) : σ₁.levelsOn s top = σ₂.levelsOn s top := by
  simp only [Context.levelsOn, h.levels, h.sideAt]

theorem leftExt (s : Side) (top p : ℕ) : σ₁.leftExt s top p = σ₂.leftExt s top p := by
  simp only [Context.leftExt, h.levelsOn, h.extPositions]

theorem rightExt (s : Side) (top p : ℕ) : σ₁.rightExt s top p = σ₂.rightExt s top p := by
  simp only [Context.rightExt, h.levelsOn, h.extPositions]

theorem chainExt (s : Side) (p q : ℕ) : σ₁.chainExt s p q = σ₂.chainExt s p q := by
  simp only [Context.chainExt, h.leftExt, h.rightExt]

theorem blocks : σ₁.blocks = σ₂.blocks := by
  simp only [Context.blocks, h.childPositions]

theorem joinExt_le (s : Side) (p q : ℕ) : σ₁.joinExt s p q ≤ σ₂.joinExt s p q := by
  unfold Context.joinExt
  rw [h.chainExt, h.levelsOn]
  refine max_le_max le_rfl ?_
  apply getD_max?_map_le
  intro N _
  rw [h.leftExt, h.rightExt]
  exact Nat.add_le_add_left (h.le N) _

theorem cupLimit_le (p q : ℕ) : σ₂.cupLimit p q ≤ σ₁.cupLimit p q := by
  unfold Context.cupLimit
  rw [← h.u, ← h.k, ← h.chainExt]
  exact min_le_min le_rfl (Nat.sub_le_sub_left (h.joinExt_le _ _ _) _)

theorem capLimit_le (p q : ℕ) : σ₂.capLimit p q ≤ σ₁.capLimit p q := by
  unfold Context.capLimit
  rw [← h.a, ← h.k, ← h.chainExt]
  exact min_le_min le_rfl (Nat.sub_le_sub_left (h.joinExt_le _ _ _) _)

theorem base_le : σ₂.base ≤ σ₁.base := by
  rw [base_eq_baseOf, base_eq_baseOf, ← h.childPositions, ← h.k]
  rcases σ₁.childPositions.head? with _ | p
  · exact le_rfl
  · exact baseOf_mono (h.cupLimit_le p p) (h.capLimit_le p p)

theorem part (keep : List ℕ) (s : Side) (m : ℕ) :
    Dominates (σ₁.part keep s m) (σ₂.part keep s m) where
  a := h.a
  u := h.u
  k := h.k
  word := by simp only [Context.part, h.letterAt, h.word]
  length := by simp only [Context.part, List.length_cons, h.length]
  le := by
    intro N
    simp only [Context.maximumAt, Context.part]
    rcases N with _ | _ | N
    · simp
    · simp
    · have := h.le (N + 1)
      simp only [Context.maximumAt, Nat.add_sub_cancel] at this
      simpa using this

end Dominates

/-- The recursion is antitone under domination, at every fuel. -/
theorem boundFuel_le (fuel : ℕ) : ∀ {σ₁ σ₂ : Context}, Dominates σ₁ σ₂ →
    boundFuel fuel σ₂ ≤ boundFuel fuel σ₁ := by
  induction fuel with
  | zero => intro σ₁ σ₂ _; simp [boundFuel]
  | succ fuel ih =>
    intro σ₁ σ₂ h
    simp only [boundFuel]
    rw [← h.numRuns]
    split_ifs with hruns
    · exact h.base_le
    · rw [← h.childPositions, ← h.blocks, ← h.k]
      apply getD_max?_le_of_forall
      intro x hx
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      obtain ⟨block, hb, d', hd', hx⟩ := hx
      rcases hx with rfl | rfl
      · refine ⟨_, ⟨block, hb, d', hd', Or.inl rfl⟩, ?_⟩
        exact Nat.add_le_add (ih (h.part _ _ _)) (ih (h.part _ _ _))
      · refine ⟨_, ⟨block, hb, d', hd', Or.inr rfl⟩, ?_⟩
        exact Nat.add_le_add (ih (h.part _ _ _)) (ih (h.part _ _ _))

theorem withMaximum_dominates (σ : Context) (l m : ℕ) :
    Dominates (σ.withMaximum l m) (σ.withMaximum l (m + 1)) where
  a := rfl
  u := rfl
  k := rfl
  word := rfl
  length := by simp [Context.withMaximum]
  le := by
    intro N
    simp only [Context.maximumAt, Context.withMaximum, List.getElem?_set]
    split_ifs <;> simp

end Context
end Ctx


namespace Ctx

/-! ### Helpers for `ctx_card_le_bound` -/

theorem nonempty_of_isDecomposableOn {n : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)}
    (h : IsDecomposableOn χ S) : S.Nonempty := by
  induction h with
  | singleton i => exact Finset.singleton_nonempty i
  | split _ _ _ ih _ => exact ih.mono Finset.subset_union_left

theorem isCupSet_singleton {n : ℕ} (χ : TripleColoring n) (i : Fin n) : IsCupSet χ {i} := by
  intro t hi hj _
  simp only [Finset.mem_singleton] at hi hj
  exact absurd (hi.trans hj.symm) (ne_of_lt t.hij)

theorem isCapSet_singleton {n : ℕ} (χ : TripleColoring n) (i : Fin n) : IsCapSet χ {i} := by
  intro t hi hj _
  simp only [Finset.mem_singleton] at hi hj
  exact absurd (hi.trans hj.symm) (ne_of_lt t.hij)

theorem isCupSet_empty {n : ℕ} (χ : TripleColoring n) : IsCupSet χ ∅ := by
  intro t hi
  simp at hi

theorem isCapSet_empty {n : ℕ} (χ : TripleColoring n) : IsCapSet χ ∅ := by
  intro t hi
  simp at hi

/-- The longest chain is at most `x` iff every chain is. -/
theorem chainMax_le_iff {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {b : Bool} {x : ℕ} :
    chainMax χ s b ≤ x ↔ ∀ C ⊆ s, (if b then IsCupSet χ C else IsCapSet χ C) → C.card ≤ x := by
  unfold chainMax
  rw [Finset.sup_le_iff]
  constructor
  · intro h C hC hb
    exact h C (by simp only [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hC, hb⟩)
  · intro h C hC
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    exact h C hC.1 hC.2

/-- Every cup of `s` is at most the longest cup of `s`. -/
theorem le_chainMax_of_isCupSet {n : ℕ} {χ : TripleColoring n} {s C : Finset (Fin n)}
    (hC : C ⊆ s) (hcup : IsCupSet χ C) : C.card ≤ chainMax χ s true :=
  chainMax_le_iff.1 le_rfl C hC (by simpa using hcup)

theorem le_chainMax_of_isCapSet {n : ℕ} {χ : TripleColoring n} {s C : Finset (Fin n)}
    (hC : C ⊆ s) (hcap : IsCapSet χ C) : C.card ≤ chainMax χ s false :=
  chainMax_le_iff.1 le_rfl C hC (by simpa using hcap)

theorem one_le_chainMax {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hs : s.Nonempty)
    (b : Bool) : 1 ≤ chainMax χ s b := by
  obtain ⟨i, hi⟩ := hs
  have hsub : ({i} : Finset (Fin n)) ⊆ s := Finset.singleton_subset_iff.2 hi
  cases b
  · exact (Finset.card_singleton i).symm.le.trans (le_chainMax_of_isCapSet hsub (isCapSet_singleton χ i))
  · exact (Finset.card_singleton i).symm.le.trans (le_chainMax_of_isCupSet hsub (isCupSet_singleton χ i))

/-- Across a deep-below split of a set satisfying `σ`, the longest cup below and the longest
cap above together stay under the strong-set limit. -/
theorem chainMax_add_chainMax_le {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    {σ : Context} (hdeep : HasDeepBelowSplit χ lower upper) (hS : Satisfies χ (lower ∪ upper) σ) :
    chainMax χ lower true + chainMax χ upper false ≤ σ.k - 1 := by
  have key : ∀ C ⊆ lower, IsCupSet χ C → ∀ D ⊆ upper, IsCapSet χ D → C.card + D.card ≤ σ.k - 1 := by
    intro C hC hcup D hD hcap
    have hstrong := hdeep.cup_union_cap_isStrongPolygonSet hC hD hcup hcap
    have hsub : C ∪ D ⊆ lower ∪ upper := Finset.union_subset_union hC hD
    have hdisj : Disjoint C D := hdeep.disjoint.mono hC hD
    rcases (C ∪ D).eq_empty_or_nonempty with hemp | hne
    · rw [Finset.union_eq_empty] at hemp
      simp [hemp.1, hemp.2]
    · have := (hS.2 (C ∪ D) hsub hne).2.2 hstrong
      rwa [Finset.card_union_of_disjoint hdisj] at this
  have hU : ∀ C ⊆ lower, IsCupSet χ C → chainMax χ upper false ≤ σ.k - 1 - C.card := by
    intro C hC hcup
    refine chainMax_le_iff.2 fun D hD hcap => ?_
    simp only [Bool.false_eq_true, if_false] at hcap
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact key C hC hcup D hD hcap)
  have hL : chainMax χ lower true ≤ σ.k - 1 - chainMax χ upper false := by
    refine chainMax_le_iff.2 fun C hC hcup => ?_
    simp only [if_true] at hcup
    have hCk : C.card ≤ σ.k - 1 := by
      simpa using key C hC hcup ∅ (Finset.empty_subset _) (isCapSet_empty χ)
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.add_le_of_le_sub hCk (hU C hC hcup))
  have hUk : chainMax χ upper false ≤ σ.k - 1 :=
    (hU ∅ (Finset.empty_subset _) (isCupSet_empty χ)).trans (Nat.sub_le _ _)
  exact Nat.add_le_of_le_sub hUk hL

theorem length_filter_le_of_imp {α : Type*} (P Q : α → Bool) (h : ∀ x, P x = true → Q x = true) :
    ∀ l : List α, (l.filter P).length ≤ (l.filter Q).length := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    by_cases hP : P x = true
    · rw [if_pos hP, if_pos (h x hP)]
      simpa using ih
    · rw [if_neg hP]
      split
      · exact ih.trans (by simp)
      · exact ih

theorem numRuns_le_length (σ : Context) : σ.numRuns ≤ σ.childPositions.length := by
  unfold Context.numRuns Context.childPositions
  apply length_filter_le_of_imp
  intro p hp
  simp only [decide_eq_true_eq] at hp ⊢
  exact hp.1

theorem one_le_baseOf {cl pl k : ℕ} (hc : 1 ≤ cl) (hp : 1 ≤ pl) : 1 ≤ Context.baseOf cl pl k := by
  unfold Context.baseOf
  rw [if_neg (by omega)]
  split
  · exact le_rfl
  · exact one_le_decomposableThreshold (by omega) (by omega)

/-- A single vertex satisfying a context forces a positive bound. -/
theorem one_le_bound_of_satisfies_singleton {n : ℕ} {χ : TripleColoring n} {i : Fin n} {σ : Context}
    (hS : Satisfies χ {i} σ) : 1 ≤ σ.bound := by
  obtain ⟨hlen, hall⟩ := hS
  rw [Finset.card_singleton] at hlen
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.1 hlen
  have hcup := (hall {i} (Finset.Subset.refl _) (Finset.singleton_nonempty i)).1 (isCupSet_singleton χ i)
  have hcap := (hall {i} (Finset.Subset.refl _) (Finset.singleton_nonempty i)).2.1 (isCapSet_singleton χ i)
  simp only [Finset.card_singleton, Finset.min'_singleton, Finset.max'_singleton, Finset.filter_singleton,
    lt_self_iff_false, if_false, Finset.card_empty, hp, List.getElem?_cons_zero, Option.getD_some] at hcup hcap
  have hruns : σ.numRuns ≤ 1 := (numRuns_le_length σ).trans hlen.le
  unfold Context.bound
  rw [hlen]
  simp only [Context.boundFuel, if_pos hruns]
  rw [Context.base_eq_baseOf, hp, List.head?_cons]
  exact one_le_baseOf hcup hcap

/-! ### Letters, levels and sides of a part -/

theorem le_getD_max?_of_mem {L : List ℕ} {x : ℕ} (hx : x ∈ L) : x ≤ (L.max?).getD 0 := by
  cases L with
  | nil => simp at hx
  | cons z zs =>
    simp only [List.max?_cons', Option.getD_some]
    exact mem_le_foldl_max z zs hx

theorem getD_max?_le {L : List ℕ} {b : ℕ} (h : ∀ x ∈ L, x ≤ b) : (L.max?).getD 0 ≤ b := by
  cases L with
  | nil => simp
  | cons z zs =>
    simp only [List.max?_cons', Option.getD_some]
    exact foldl_max_le b zs z (h z (List.mem_cons_self ..)) fun y hy => h y (List.mem_cons.2 (Or.inr hy))

namespace Context

theorem letterAt_of_length_le (σ : Context) {p : ℕ} (h : σ.word.length ≤ p) :
    σ.letterAt p = Letter.child := by
  simp [Context.letterAt, List.getElem?_eq_none h]

theorem part_word_length (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).word.length = σ.word.length := by
  simp [Context.part]

theorem part_letterAt_of_child (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) {p : ℕ}
    (hp : p < σ.word.length) (hσ : σ.letterAt p = Letter.child) :
    (σ.part keep s m).letterAt p = if p ∈ keep then Letter.child else Letter.ext 1 s := by
  unfold Context.letterAt at hσ ⊢
  simp only [Context.letterAt, Context.part, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, hσ]

theorem part_letterAt_of_ext (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) {p l : ℕ} {s' : Side}
    (hp : p < σ.word.length) (hσ : σ.letterAt p = Letter.ext l s') :
    (σ.part keep s m).letterAt p = Letter.ext (l + 1) s' := by
  unfold Context.letterAt at hσ ⊢
  simp only [Context.letterAt, Context.part, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some, hσ]

theorem part_maxima (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).maxima = m :: σ.maxima := rfl

theorem part_k (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) : (σ.part keep s m).k = σ.k := rfl

theorem part_extPositions_succ (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) {l : ℕ}
    (hl : 1 ≤ l) : (σ.part keep s m).extPositions (l + 1) = σ.extPositions l := by
  unfold Context.extPositions
  rw [part_word_length]
  apply List.filter_congr
  intro p hp
  rw [List.mem_range] at hp
  rcases hσ : σ.letterAt p with _ | ⟨l₀, s₀⟩
  · rw [part_letterAt_of_child σ keep s m hp hσ]
    by_cases hmem : p ∈ keep
    · simp [hmem]
    · simp only [hmem, if_false]
      simp <;> omega
  · rw [part_letterAt_of_ext σ keep s m hp hσ]
    simp

theorem part_sideAt_succ (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    (σ.part keep s m).sideAt (l + 1) = σ.sideAt l := by
  unfold Context.sideAt
  rw [part_extPositions_succ σ keep s m hl]
  rcases hh : (σ.extPositions l).head? with _ | q
  · rfl
  · have hq := List.mem_of_mem_head? (Option.mem_def.2 hh)
    simp only [Context.extPositions, List.mem_filter, List.mem_range] at hq
    obtain ⟨hqlen, hq⟩ := hq
    dsimp only
    rcases hσ : σ.letterAt q with _ | ⟨l₀, s₀⟩
    · simp [hσ] at hq
    · rw [part_letterAt_of_ext σ keep s m hqlen hσ]

/-- With no level-zero letters in `σ`, every level-one letter of a part carries the part's side. -/
theorem part_letterAt_of_mem_extPositions_one {σ : Context}
    (hlet : ∀ p l s', σ.letterAt p = Letter.ext l s' → 1 ≤ l) (keep : List ℕ) (s : Side) (m : ℕ)
    {q : ℕ} (hq : q ∈ (σ.part keep s m).extPositions 1) :
    (σ.part keep s m).letterAt q = Letter.ext 1 s := by
  simp only [Context.extPositions, List.mem_filter, List.mem_range, part_word_length] at hq
  obtain ⟨hqlen, hq⟩ := hq
  rcases hσ : σ.letterAt q with _ | ⟨l₀, s₀⟩
  · rw [part_letterAt_of_child σ keep s m hqlen hσ] at hq ⊢
    by_cases hmem : q ∈ keep
    · simp [hmem] at hq
    · simp [hmem]
  · have := hlet q l₀ s₀ hσ
    rw [part_letterAt_of_ext σ keep s m hqlen hσ] at hq
    simp at hq
    omega

theorem part_sideAt_one_of_mem {σ : Context}
    (hlet : ∀ p l s', σ.letterAt p = Letter.ext l s' → 1 ≤ l) (keep : List ℕ) (s : Side) (m : ℕ)
    {q : ℕ} (hq : q ∈ (σ.part keep s m).extPositions 1) : (σ.part keep s m).sideAt 1 = s := by
  unfold Context.sideAt
  rcases hh : ((σ.part keep s m).extPositions 1).head? with _ | r
  · rw [List.head?_eq_none_iff] at hh
    rw [hh] at hq
    simp at hq
  · have hr := part_letterAt_of_mem_extPositions_one hlet keep s m (List.mem_of_mem_head? (Option.mem_def.2 hh))
    simp only [hr]

theorem part_sideAt_one_lower {σ : Context}
    (hlet : ∀ p l s', σ.letterAt p = Letter.ext l s' → 1 ≤ l) (keep : List ℕ) (m : ℕ) :
    (σ.part keep Side.lower m).sideAt 1 = Side.lower := by
  rcases hh : ((σ.part keep Side.lower m).extPositions 1).head? with _ | r
  · unfold Context.sideAt
    rw [hh]
  · exact part_sideAt_one_of_mem hlet keep Side.lower m (List.mem_of_mem_head? (Option.mem_def.2 hh))

/-- Well-formedness passes to parts with an admissible new maximum. -/
theorem WellFormed.part {σ : Context} (hwf : σ.WellFormed) (keep : List ℕ) (s : Side)
    {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ σ.k - 2) : (σ.part keep s m).WellFormed := by
  obtain ⟨ha, hu, hak, huk, hmax, hlet⟩ := hwf
  have hlet1 : ∀ p l s', σ.letterAt p = Letter.ext l s' → 1 ≤ l := fun p l s' h => (hlet p l s' h).1
  refine ⟨ha, hu, hak, huk, ?_, ?_⟩
  · intro x hx
    simp only [part_maxima, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hm1, hmk⟩
    · exact hmax x hx
  · intro p l s' hp
    have hplen : p < σ.word.length := by
      by_contra hge
      rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
      cases hp
    have hmem : p ∈ (σ.part keep s m).extPositions l := by
      simp only [Context.extPositions, List.mem_filter, List.mem_range, part_word_length]
      exact ⟨hplen, by simp [hp]⟩
    rcases hσ : σ.letterAt p with _ | ⟨l₀, s₀⟩
    · rw [part_letterAt_of_child σ keep s m hplen hσ] at hp
      by_cases hk : p ∈ keep
      · simp [hk] at hp
      · simp only [hk, if_false, Letter.ext.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        refine ⟨le_rfl, by simp [part_maxima], ?_⟩
        exact (part_sideAt_one_of_mem hlet1 keep s m hmem).symm
    · rw [part_letterAt_of_ext σ keep s m hplen hσ] at hp
      simp only [Letter.ext.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨hl1, hllen, hside⟩ := hlet p l₀ s₀ hσ
      refine ⟨by omega, by simp [part_maxima]; omega, ?_⟩
      rw [part_sideAt_succ σ keep s m hl1]
      exact hside

/-! ### Changing the level-one maximum -/

theorem sideAt_withMaximum (σ : Context) (l m l' : ℕ) : (σ.withMaximum l m).sideAt l' = σ.sideAt l' := rfl

theorem extPositions_withMaximum (σ : Context) (l m l' : ℕ) :
    (σ.withMaximum l m).extPositions l' = σ.extPositions l' := rfl

theorem levels_withMaximum (σ : Context) (l m : ℕ) : (σ.withMaximum l m).levels = σ.levels := by
  simp [Context.levels, Context.withMaximum]

theorem levelsOn_withMaximum (σ : Context) (l m : ℕ) (s : Side) (top : ℕ) :
    (σ.withMaximum l m).levelsOn s top = σ.levelsOn s top := by
  unfold Context.levelsOn
  exact congrArg _ (levels_withMaximum σ l m)

theorem leftExt_withMaximum (σ : Context) (l m : ℕ) (s : Side) (top p : ℕ) :
    (σ.withMaximum l m).leftExt s top p = σ.leftExt s top p := by
  simp only [Context.leftExt, levelsOn_withMaximum, extPositions_withMaximum]

theorem rightExt_withMaximum (σ : Context) (l m : ℕ) (s : Side) (top p : ℕ) :
    (σ.withMaximum l m).rightExt s top p = σ.rightExt s top p := by
  simp only [Context.rightExt, levelsOn_withMaximum, extPositions_withMaximum]

theorem chainExt_withMaximum (σ : Context) (l m : ℕ) (s : Side) (p q : ℕ) :
    (σ.withMaximum l m).chainExt s p q = σ.chainExt s p q := by
  simp only [Context.chainExt, leftExt_withMaximum, rightExt_withMaximum]

theorem maximumAt_withMaximum_one_of_two_le (σ : Context) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    (σ.withMaximum 1 m).maximumAt N = σ.maximumAt N := by
  simp only [Context.maximumAt, Context.withMaximum]
  rw [List.getElem?_set_ne (by omega)]

theorem maximumAt_withMaximum_one_self (σ : Context) (m : ℕ) (h : 0 < σ.maxima.length) :
    (σ.withMaximum 1 m).maximumAt 1 = m := by
  simp [Context.maximumAt, Context.withMaximum, List.getElem?_set_self h]

theorem one_le_of_mem_levelsOn {σ : Context} {s : Side} {top N : ℕ} (h : N ∈ σ.levelsOn s top) :
    1 ≤ N ∧ 0 < σ.maxima.length ∧ σ.sideAt N = s := by
  simp only [Context.levelsOn, Context.levels, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨i, hi, rfl⟩, hs, _⟩ := h
  exact ⟨by omega, by omega, hs⟩

theorem levelsOn_one (σ : Context) (s : Side) : σ.levelsOn s 1 = [] := by
  simp only [Context.levelsOn, Context.levels, List.filter_eq_nil_iff, List.mem_map, List.mem_range,
    decide_eq_true_eq, not_and, not_or]
  rintro l ⟨i, hi, rfl⟩ _
  omega

theorem leftExt_one (σ : Context) (s : Side) (p : ℕ) : σ.leftExt s 1 p = 0 := by
  simp [Context.leftExt, levelsOn_one]

theorem rightExt_one (σ : Context) (s : Side) (p : ℕ) : σ.rightExt s 1 p = 0 := by
  simp [Context.rightExt, levelsOn_one]

/-- The join extension after changing the level-one maximum is at most the old one or the
new maximum: the new maximum only enters the level-one term, whose extensions are empty. -/
theorem joinExt_withMaximum_one_le (σ : Context) (m : ℕ) (s : Side) (p q : ℕ) :
    (σ.withMaximum 1 m).joinExt s p q ≤ max (σ.joinExt s p q) m := by
  unfold Context.joinExt
  rw [chainExt_withMaximum, levelsOn_withMaximum]
  refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
  apply getD_max?_le
  intro x hx
  obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hx
  rw [leftExt_withMaximum, rightExt_withMaximum]
  obtain ⟨hN1, hlen, _⟩ := one_le_of_mem_levelsOn hN
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    rw [leftExt_one, rightExt_one, maximumAt_withMaximum_one_self σ m hlen]
    simp
  · rw [maximumAt_withMaximum_one_of_two_le σ m h]
    exact le_max_of_le_left (le_max_of_le_right (le_getD_max?_of_mem (List.mem_map.2 ⟨N, hN, rfl⟩)))

theorem joinExt_withMaximum_one_of_sideAt_ne (σ : Context) (m : ℕ) {s : Side}
    (hs : σ.sideAt 1 ≠ s) (p q : ℕ) : (σ.withMaximum 1 m).joinExt s p q = σ.joinExt s p q := by
  unfold Context.joinExt
  rw [chainExt_withMaximum, levelsOn_withMaximum]
  have hmap : List.map (fun N => (σ.withMaximum 1 m).leftExt s N p + (σ.withMaximum 1 m).rightExt s N q
      + (σ.withMaximum 1 m).maximumAt N) (σ.levelsOn s 0) =
      List.map (fun N => σ.leftExt s N p + σ.rightExt s N q + σ.maximumAt N) (σ.levelsOn s 0) := by
    apply List.map_congr_left
    intro N hN
    obtain ⟨hN1, _, hside⟩ := one_le_of_mem_levelsOn hN
    have h2 : 2 ≤ N := by
      rcases Nat.lt_or_ge N 2 with h | h
      · have : N = 1 := by omega
        subst this
        exact absurd hside hs
      · exact h
    rw [leftExt_withMaximum, rightExt_withMaximum, maximumAt_withMaximum_one_of_two_le σ m h2]
  rw [hmap]

theorem childPositions_withMaximum (σ : Context) (l m : ℕ) :
    (σ.withMaximum l m).childPositions = σ.childPositions := rfl

/-- Strengthening the level-one maximum of a context whose level one is on the lower side is
sound when every cup of the set is short enough. -/
theorem satisfies_withMaximum_one_of_cup_le {n : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)}
    {σ : Context} {m : ℕ} (hS : Satisfies χ S σ) (hside : σ.sideAt 1 = Side.lower)
    (hcup : ∀ C ⊆ S, IsCupSet χ C → C.card ≤ σ.k - 1 - m) :
    Satisfies χ S (σ.withMaximum 1 m) := by
  obtain ⟨hlen, hall⟩ := hS
  refine ⟨hlen, ?_⟩
  intro C hC hCne
  obtain ⟨h1, h2, h3⟩ := hall C hC hCne
  refine ⟨fun hc => ?_, fun hc => ?_, h3⟩
  · have hlim := h1 hc
    have hk := hcup C hC hc
    unfold Context.cupLimit at hlim ⊢
    rw [chainExt_withMaximum]
    refine le_min (hlim.trans (min_le_left _ _)) ?_
    have hj := joinExt_withMaximum_one_le σ m Side.lower
      ((σ.childPositions[(S.filter (· < C.min' hCne)).card]?).getD 0)
      ((σ.childPositions[(S.filter (· < C.max' hCne)).card]?).getD 0)
    have h2' := hlim.trans (min_le_right _ _)
    calc C.card ≤ σ.k - 1 - max (σ.joinExt Side.lower _ _) m := by
          rcases le_total (σ.joinExt Side.lower
              ((σ.childPositions[(S.filter (· < C.min' hCne)).card]?).getD 0)
              ((σ.childPositions[(S.filter (· < C.max' hCne)).card]?).getD 0)) m with h | h
          · rw [max_eq_right h]
            exact hk
          · rw [max_eq_left h]
            exact h2'
      _ ≤ _ := Nat.sub_le_sub_left hj _
  · have hlim := h2 hc
    unfold Context.capLimit at hlim ⊢
    rw [chainExt_withMaximum, joinExt_withMaximum_one_of_sideAt_ne σ m (by rw [hside]; decide)]
    exact hlim

theorem part_eq_withMaximum_one (σ : Context) (keep : List ℕ) (s : Side) (m m' : ℕ) :
    σ.part keep s m' = (σ.part keep s m).withMaximum 1 m' := by
  simp [Context.part, Context.withMaximum]

end Context

/-- Strengthening the sibling maximum of a lower part is sound when the part's own cups are
short enough: the new maximum only enters the level-one join term. -/
theorem satisfies_part_lower_of_cup_le {n : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)}
    {σ : Context} (hwf : σ.WellFormed) {keep : List ℕ} {m m' : ℕ}
    (hS : Satisfies χ S (σ.part keep Side.lower m))
    (hcup : ∀ C ⊆ S, IsCupSet χ C → C.card ≤ σ.k - 1 - m') :
    Satisfies χ S (σ.part keep Side.lower m') := by
  rw [Context.part_eq_withMaximum_one σ keep Side.lower m m']
  exact Context.satisfies_withMaximum_one_of_cup_le hS
    (Context.part_sideAt_one_lower (fun p l s' h => (hwf.2.2.2.2.2 p l s' h).1) keep m) hcup

namespace Context

theorem childPositions_pairwise (σ : Context) : σ.childPositions.Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem childPositions_nodup (σ : Context) : σ.childPositions.Nodup :=
  List.nodup_range.filter _

/-- The rank of a vertex of `S` is below `S.card`. -/
theorem rank_lt_card {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    (S.filter (· < v)).card < S.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨v, hv, lt_irrefl v⟩)

theorem rank_lt_rank {n : ℕ} {S : Finset (Fin n)} {v w : Fin n} (hv : v ∈ S) (hvw : v < w) :
    (S.filter (· < v)).card < (S.filter (· < w)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨v, Finset.mem_filter.2 ⟨hv, hvw⟩, by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hvw⟩

/-- The position of a vertex of `S` is a child position. -/
theorem pos_mem_childPositions {n : ℕ} {S : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) {v : Fin n} (hv : v ∈ S) :
    (σ.childPositions[(S.filter (· < v)).card]?).getD 0 ∈ σ.childPositions := by
  have h : (S.filter (· < v)).card < σ.childPositions.length := hlen ▸ rank_lt_card hv
  rw [List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem pos_injOn {n : ℕ} {S : Finset (Fin n)} {σ : Context} (hlen : σ.childPositions.length = S.card) :
    Set.InjOn (fun v : Fin n => (σ.childPositions[(S.filter (· < v)).card]?).getD 0) S := by
  have key : ∀ v ∈ S, ∀ w ∈ S, v < w →
      (σ.childPositions[(S.filter (· < v)).card]?).getD 0 ≠ (σ.childPositions[(S.filter (· < w)).card]?).getD 0 := by
    intro v hv w hw hvw
    have h1 : (S.filter (· < v)).card < σ.childPositions.length := hlen ▸ rank_lt_card hv
    have h2 : (S.filter (· < w)).card < σ.childPositions.length := hlen ▸ rank_lt_card hw
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some]
    exact ne_of_lt ((List.pairwise_iff_getElem.1 (childPositions_pairwise σ)) _ _ h1 h2 (rank_lt_rank hv hvw))
  intro v hv w hw hvw
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key v hv w hw h hvw
  · exact key w hw v hv h hvw.symm

theorem mem_positionsOf {n : ℕ} {S T : Finset (Fin n)} (σ : Context) {p : ℕ} :
    p ∈ σ.positionsOf S T ↔ ∃ v ∈ T, (σ.childPositions[(S.filter (· < v)).card]?).getD 0 = p := by
  simp [Context.positionsOf, Finset.mem_sort, Finset.mem_image]

end Context

theorem positionsOf_subset {n : ℕ} {S T : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) (hT : T ⊆ S) :
    ∀ p ∈ σ.positionsOf S T, p ∈ σ.childPositions := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := (Context.mem_positionsOf σ).1 hp
  exact Context.pos_mem_childPositions hlen (hT hv)

theorem positionsOf_ne_nil {n : ℕ} {S T : Finset (Fin n)} (σ : Context) (hT : T.Nonempty) :
    σ.positionsOf S T ≠ [] := by
  intro h
  obtain ⟨v, hv⟩ := hT
  have : (σ.childPositions[(S.filter (· < v)).card]?).getD 0 ∈ σ.positionsOf S T :=
    (Context.mem_positionsOf σ).2 ⟨v, hv, rfl⟩
  rw [h] at this
  simp at this

theorem positionsOf_length_lt {n : ℕ} {lower upper : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = (lower ∪ upper).card) (hdisj : Disjoint lower upper)
    (hu : upper.Nonempty) : (σ.positionsOf (lower ∪ upper) lower).length < σ.childPositions.length := by
  rw [Context.positionsOf, Finset.length_sort, hlen, Finset.card_union_of_disjoint hdisj]
  have h1 := Finset.card_image_le (s := lower)
    (f := fun v => (σ.childPositions[((lower ∪ upper).filter (· < v)).card]?).getD 0)
  have h2 := hu.card_pos
  omega

theorem positionsOf_compl {n : ℕ} {lower upper : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = (lower ∪ upper).card) (hdisj : Disjoint lower upper) :
    σ.childPositions.filter (fun p => p ∉ σ.positionsOf (lower ∪ upper) lower) =
      σ.positionsOf (lower ∪ upper) upper := by
  set f : Fin n → ℕ := fun v => (σ.childPositions[((lower ∪ upper).filter (· < v)).card]?).getD 0 with hf
  have hinj : Set.InjOn f (↑(lower ∪ upper) : Set (Fin n)) := Context.pos_injOn hlen
  have hsubL : lower.image f ⊆ σ.childPositions.toFinset := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    exact List.mem_toFinset.2 (Context.pos_mem_childPositions hlen (Finset.mem_union_left _ hv))
  have hsubU : upper.image f ⊆ σ.childPositions.toFinset := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    exact List.mem_toFinset.2 (Context.pos_mem_childPositions hlen (Finset.mem_union_right _ hv))
  have hdisjI : Disjoint (lower.image f) (upper.image f) := by
    rw [Finset.disjoint_left]
    intro p hpL hpU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hpL
    obtain ⟨w, hw, hvw⟩ := Finset.mem_image.1 hpU
    have := hinj (Finset.mem_union_right _ hw) (Finset.mem_union_left _ hv) hvw
    subst this
    exact Finset.disjoint_left.1 hdisj hv hw
  have hcardL : (lower.image f).card = lower.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 Finset.subset_union_left))
  have hcardU : (upper.image f).card = upper.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 Finset.subset_union_right))
  have hunion : lower.image f ∪ upper.image f = σ.childPositions.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hsubL hsubU)
    rw [List.toFinset_card_of_nodup (Context.childPositions_nodup σ), hlen,
      Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hdisjI, hcardL, hcardU]
  have hmem : ∀ p, p ∈ σ.childPositions.filter (fun q => q ∉ σ.positionsOf (lower ∪ upper) lower) ↔
      p ∈ σ.positionsOf (lower ∪ upper) upper := by
    intro p
    rw [List.mem_filter, decide_eq_true_eq, Context.mem_positionsOf, Context.mem_positionsOf]
    constructor
    · rintro ⟨hp, hnot⟩
      have hp' : p ∈ lower.image f ∪ upper.image f := hunion ▸ List.mem_toFinset.2 hp
      rcases Finset.mem_union.1 hp' with h | h
      · obtain ⟨v, hv, hvp⟩ := Finset.mem_image.1 h
        exact absurd ⟨v, hv, hvp⟩ hnot
      · obtain ⟨v, hv, hvp⟩ := Finset.mem_image.1 h
        exact ⟨v, hv, hvp⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨Context.pos_mem_childPositions hlen (Finset.mem_union_right _ hv), ?_⟩
      rintro ⟨w, hw, hwv⟩
      have := hinj (Finset.mem_union_left _ hw) (Finset.mem_union_right _ hv) hwv
      subst this
      exact Finset.disjoint_left.1 hdisj hw hv
  have hperm : (σ.childPositions.filter (fun q => q ∉ σ.positionsOf (lower ∪ upper) lower)).Perm
      (σ.positionsOf (lower ∪ upper) upper) :=
    (List.perm_ext_iff_of_nodup ((Context.childPositions_nodup σ).filter _) (Finset.sort_nodup _ _)).2 hmem
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (((Context.childPositions_pairwise σ).imp le_of_lt).filter _) (Finset.pairwise_sort _ _) hperm

end Ctx

end ErdosSzekeres

end
