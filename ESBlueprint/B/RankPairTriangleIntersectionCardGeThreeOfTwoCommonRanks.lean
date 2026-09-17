import Mathlib.Data.Finset.Prod

namespace ErdosSzekeres

/-- If two finite natural-rank sets share two distinct ranks, then their nondecreasing ordered-pair triangles share at least three pairs: the two diagonals and the sorted cross-pair. This amplifies two common ranks into the exact quadratic overlap needed by mixed-capacity collision counting.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks (A B : Finset ℕ) (r q : ℕ) (hne : r ≠ q) (hrA : r ∈ A) (hqA : q ∈ A) (hrB : r ∈ B) (hqB : q ∈ B) : let pairs : Finset ℕ → Finset (ℕ × ℕ) := fun S => (S.product S).filter (fun z => z.1 ≤ z.2); 3 ≤ ((pairs A) ∩ (pairs B)).card := by
  classical
  dsimp only
  by_cases hrq : r < q
  · let T : Finset (ℕ × ℕ) := {(r, r), (r, q), (q, q)}
    have hcard : T.card = 3 := by
      simp [T, hne]
    have hsub : T ⊆
        ((A.product A).filter (fun z => z.1 ≤ z.2)) ∩
          ((B.product B).filter (fun z => z.1 ≤ z.2)) := by
      intro z hz
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp [hrA, hqA, hrB, hqB, hrq.le]
    rw [← hcard]
    exact Finset.card_le_card hsub
  · have hqr : q < r := by omega
    let T : Finset (ℕ × ℕ) := {(q, q), (q, r), (r, r)}
    have hcard : T.card = 3 := by
      simp [T, hqr.ne]
    have hsub : T ⊆
        ((A.product A).filter (fun z => z.1 ≤ z.2)) ∩
          ((B.product B).filter (fun z => z.1 ≤ z.2)) := by
      intro z hz
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp [hrA, hqA, hrB, hqB, hqr.le]
    rw [← hcard]
    exact Finset.card_le_card hsub

end ErdosSzekeres
