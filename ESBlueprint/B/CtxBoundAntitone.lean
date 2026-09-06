import ErdosSzekeres.DecomposableContext

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

/-- Monotonicity of the context bound in a sibling maximum: raising the longest chain of the sibling at any level does not increase the bound (every limit entering the recursion is antitone in the maxima). Tested on 9,444 comparisons (experiment 0121).
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_card_le_bound -/
theorem ctx_bound_antitone (σ : Ctx.Context) (l m : ℕ) : (σ.withMaximum l (m + 1)).bound ≤ (σ.withMaximum l m).bound := by
  exact Ctx.Context.boundFuel_le _ (Ctx.Context.withMaximum_dominates σ l m)

end ErdosSzekeres
