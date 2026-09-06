import ErdosSzekeres.E3FiniteReduction
import ESBlueprint.B.CtxCardLeBound

namespace ErdosSzekeres

namespace Ctx
namespace Context

/-! ### The root context -/

theorem root_word_length (a u k s : ℕ) : (Context.root a u k s).word.length = s := by
  simp [Context.root]

theorem root_k (a u k s : ℕ) : (Context.root a u k s).k = k := rfl

theorem root_letterAt (a u k s p : ℕ) : (Context.root a u k s).letterAt p = Letter.child := by
  simp only [Context.letterAt, Context.root, List.getElem?_replicate]
  split <;> simp

theorem root_childPositions (a u k s : ℕ) : (Context.root a u k s).childPositions = List.range s := by
  unfold Context.childPositions
  rw [root_word_length]
  apply List.filter_eq_self.2
  intro p _
  simp [root_letterAt]

theorem root_numRuns_le (a u k s : ℕ) : (Context.root a u k s).numRuns ≤ 1 := by
  unfold Context.numRuns
  rw [root_word_length]
  have hsub : (List.range s).filter (fun p => decide ((Context.root a u k s).letterAt p = Letter.child ∧
      (p = 0 ∨ (Context.root a u k s).letterAt (p - 1) ≠ Letter.child))) ⊆ [0] := by
    intro p hp
    rw [List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨_, _, h⟩ := hp
    rcases h with rfl | h
    · simp
    · exact absurd (root_letterAt a u k s (p - 1)) h
  exact ((List.nodup_range.filter _).subperm hsub).length_le

theorem root_levelsOn (a u k s : ℕ) (sd : Side) (top : ℕ) :
    (Context.root a u k s).levelsOn sd top = [] := by
  simp [Context.levelsOn, Context.levels, Context.root]

theorem root_leftExt (a u k s : ℕ) (sd : Side) (top p : ℕ) :
    (Context.root a u k s).leftExt sd top p = 0 := by
  simp [Context.leftExt, root_levelsOn]

theorem root_rightExt (a u k s : ℕ) (sd : Side) (top p : ℕ) :
    (Context.root a u k s).rightExt sd top p = 0 := by
  simp [Context.rightExt, root_levelsOn]

theorem root_chainExt (a u k s : ℕ) (sd : Side) (p q : ℕ) :
    (Context.root a u k s).chainExt sd p q = 0 := by
  simp [Context.chainExt, root_leftExt, root_rightExt]

theorem root_joinExt (a u k s : ℕ) (sd : Side) (p q : ℕ) :
    (Context.root a u k s).joinExt sd p q = 0 := by
  simp [Context.joinExt, root_chainExt, root_levelsOn]

theorem root_cupLimit (a u k s p q : ℕ) :
    (Context.root a u k s).cupLimit p q = min (u - 1) (k - 1) := by
  simp only [Context.cupLimit, root_chainExt, root_joinExt, Nat.sub_zero]
  rfl

theorem root_capLimit (a u k s p q : ℕ) :
    (Context.root a u k s).capLimit p q = min (a - 1) (k - 1) := by
  simp only [Context.capLimit, root_chainExt, root_joinExt, Nat.sub_zero]
  rfl

theorem root_wellFormed {a u k : ℕ} (s : ℕ) (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    (Context.root a u k s).WellFormed := by
  refine ⟨ha, hu, hak, huk, ?_, ?_⟩
  · intro m hm
    simp [Context.root] at hm
  · intro p l sd h
    rw [root_letterAt] at h
    cases h

theorem baseOf_le_threshold {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) :
    Context.baseOf (u - 1) (a - 1) k ≤ decomposableThreshold a u k := by
  unfold Context.baseOf
  rw [if_neg (by omega)]
  split_ifs with h1
  · exact one_le_decomposableThreshold ha hu
  · rw [show a - 1 + 1 = a by omega, show u - 1 + 1 = u by omega]

/-- The bound of the root context is the classical threshold (or less, for no vertex). -/
theorem root_bound_le {a u k : ℕ} (s : ℕ) (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    (Context.root a u k s).bound ≤ decomposableThreshold a u k := by
  unfold Context.bound
  rw [Context.boundFuel.eq_2, if_pos (root_numRuns_le a u k s), Context.base_eq_baseOf,
    root_childPositions]
  rcases s with _ | s
  · simp
  · rw [List.range_succ_eq_map, List.head?_cons]
    simp only [root_cupLimit, root_capLimit, root_k]
    rw [min_eq_left (by omega), min_eq_left (by omega)]
    exact baseOf_le_threshold ha hu

end Context

/-- A set with no `u`-cup, no `a`-cap and no strong `k`-set satisfies the root context. -/
theorem satisfies_root {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {a u k : ℕ}
    (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hcup : ¬ ContainsCupSet χ s u) (hcap : ¬ ContainsCapSet χ s a)
    (hstrong : ¬ ContainsStrongPolygonSet χ s k) :
    Satisfies χ s (Context.root a u k s.card) := by
  refine ⟨by simp [Context.root_childPositions], ?_⟩
  intro C hC hCne
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show C.card ≤ (Context.root a u k s.card).cupLimit _ _
    rw [Context.root_cupLimit, min_eq_left (by omega)]
    by_contra hlt
    obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ C.card by omega)
    exact hcup ⟨D, hD.trans hC, hDcard, FinsetPolygon.IsCupSet.mono h hD⟩
  · show C.card ≤ (Context.root a u k s.card).capLimit _ _
    rw [Context.root_capLimit, min_eq_left (by omega)]
    by_contra hlt
    obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq (show a ≤ C.card by omega)
    exact hcap ⟨D, hD.trans hC, hDcard, FinsetPolygon.IsCapSet.mono h hD⟩
  · show C.card ≤ (Context.root a u k s.card).k - 1
    rw [Context.root_k]
    by_contra hlt
    obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq (show k ≤ C.card by omega)
    exact hstrong ⟨D, hD.trans hC, hDcard, FinsetPolygon.IsStrongPolygonSet.mono h hD⟩

end Ctx

/-- The decomposable theorem (Baek–Balko Theorem 8) for all parameters: a decomposable coloring on more than decomposableThreshold a u k vertices contains an a-cap, a u-cup, or a strong k-set. The degenerate a = 1 / u = 1 cases are to be checked against containsCupSet_one before this statement is locked.
@node
@ws B
@kind formalization
@dangling-ok uniform theorem; consumer is E3FiniteReduction's DecomposableExactUpperAt
@measure a + u (published induction) -/
theorem decomposableStateUpper_all (a u k : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k) : DecomposableStateUpper a u k := by
  unfold DecomposableStateUpper
  intro n χ s hdec hlt
  by_contra hno
  push Not at hno
  obtain ⟨hcap, hcup, hstrong⟩ := hno
  have hne : s.Nonempty := Finset.card_pos.1 (by omega)
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have : a = 1 := by omega
    subst this
    exact hcap (containsCapSet_one hne)
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · have : u = 1 := by omega
    subst this
    exact hcup (containsCupSet_one hne)
  have hS := Ctx.satisfies_root ha hu hak huk hcup hcap hstrong
  have hb := ctx_card_le_bound (Ctx.Context.root a u k s.card)
    (Ctx.Context.root_wellFormed s.card ha2 hu2 hak huk) hdec hS
  have := Ctx.Context.root_bound_le (a := a) (u := u) (k := k) s.card ha2 hu2 hak huk
  omega


end ErdosSzekeres
