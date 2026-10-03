import ErdosSzekeres.PublishedInductionSemantics
import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Every legal adjacent-singleton split is bounded by the parent decomposable threshold. Classical monotonicity and Pascal handle the inactive regime; certified prefix/suffix allocations handle the active window.
@node
@ws B
@kind formalization
@dangling-ok Together with decomposableThreshold_split_attained proves the exact splitting identity needed for R19 PEEL -/
theorem decomposableThreshold_split_le (a u k d : ℕ) (ha : 3 ≤ a) (hu : 3 ≤ u) (hak : a ≤ k) (huk : u ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k - 2) : decomposableThreshold a (min (u - 1) (k - d)) k + decomposableThreshold (min (a - 1) (d + 1)) u k ≤ decomposableThreshold a u k := by
  have hleft : 2 ≤ min (u - 1) (k - d) := by omega
  have hright : 2 ≤ min (a - 1) (d + 1) := by omega
  by_cases hclass : a + u ≤ k + 3
  · calc
      decomposableThreshold a (min (u - 1) (k - d)) k +
          decomposableThreshold (min (a - 1) (d + 1)) u k ≤
          decomposableThreshold a (u - 1) k + decomposableThreshold (a - 1) u k :=
        Nat.add_le_add
          (decomposableThreshold_mono (by omega) hleft (by omega) (by omega))
          (decomposableThreshold_mono hright (by omega) (by omega) (by omega))
      _ = decomposableThreshold a u k := by
        rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
          decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
          decomposableThreshold_eq_choose (by omega) (by omega) hclass]
        rw [show a + (u - 1) - 4 = a + u - 5 by omega,
          show a - 1 + u - 4 = a + u - 5 by omega,
          show a + u - 4 = (a + u - 5) + 1 by omega,
          show a - 2 = (a - 3) + 1 by omega,
          show a - 1 - 2 = a - 3 by omega, Nat.choose_succ_succ]
        simp only [Nat.succ_eq_add_one]
        omega
  · have h := published_nonsaturated_next_threshold_pair_le
      (a := a) (u := u) (k := k)
      (a' := min (a - 1) (d + 1) - 1) (u' := min (u - 1) (k - d) - 1)
      (by omega) (by omega) hak huk (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    simpa only [show min (u - 1) (k - d) - 1 + 1 = min (u - 1) (k - d) by omega,
      show min (a - 1) (d + 1) - 1 + 1 = min (a - 1) (d + 1) by omega] using h


end ErdosSzekeres
