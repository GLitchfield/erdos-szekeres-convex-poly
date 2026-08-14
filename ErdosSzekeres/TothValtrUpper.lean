module

public import ErdosSzekeres.TothValtrFrameProducer
public import Mathlib.Data.Nat.Choose.Central

@[expose] public section

/-!
# The Tóth--Valtr upper bound

This file combines the explicit `TothValtrFrame` producer with the exact
cup--cap recurrence, and proves the resulting unconditional forcing bound and
its strict improvement over the classical binomial threshold.
-/

namespace ErdosSzekeres

/-- A Tóth--Valtr frame on a sufficiently large set produces an `n`-point
convex subset. -/
theorem containsConvexSubset_of_tothValtrFrame
    {s : Finset (Point 2)} {n : ℕ} (hn : 3 ≤ n)
    (hframe : TothValtrFrame s)
    (hcard : Nat.choose (2 * n - 5) (n - 2) + 2 ≤ s.card) :
    ContainsConvexSubset s n := by
  obtain ⟨q, hqcard, P, hcupTransfer, hcapTransfer⟩ := hframe
  have hsum : (n - 1) + n - 4 = 2 * n - 5 := by omega
  have hindex : (n - 1) - 2 = n - 3 := by omega
  have hchoose :
      Nat.choose ((n - 1) + n - 4) ((n - 1) - 2) =
        Nat.choose (2 * n - 5) (n - 2) := by
    rw [hsum, hindex]
    exact Nat.choose_symm_of_eq_add (by omega)
  have hlarge :
      Nat.choose ((n - 1) + n - 4) ((n - 1) - 2) < q.card := by
    rw [hchoose]
    omega
  rcases CupCap.SweptConfiguration.hasCap_or_hasCup
      P.configuration (a := n - 1) (b := n) (by omega) (by omega) hlarge with
    hcap | hcup
  · have htarget := hcapTransfer hcap
    rw [show n - 1 + 1 = n by omega] at htarget
    exact htarget
  · exact hcupTransfer hcup

/-- The published forcing bound follows from a uniform producer for
`TothValtrFrame`. -/
theorem forcesConvexPolygon_tothValtr_of_frame
    (n : ℕ) (hn : 3 ≤ n)
    (hframe : ∀ s : Finset (Point 2), s.Nonempty →
      InGeneralPosition s → TothValtrFrame s) :
    ForcesConvexPolygon n (Nat.choose (2 * n - 5) (n - 2) + 2) := by
  intro s hcard hgp
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  exact containsConvexSubset_of_tothValtrFrame hn (hframe s hs hgp) hcard

/-- The explicit Tóth--Valtr uniform upper bound for planar point sets in
general position. -/
theorem tothValtr_upper (n : ℕ) (hn : 3 ≤ n) :
    ForcesConvexPolygon n (Nat.choose (2 * n - 5) (n - 2) + 2) := by
  apply forcesConvexPolygon_tothValtr_of_frame n hn
  exact exists_tothValtrFrame

private theorem choose_double_eq_two_mul_choose_pred (m : ℕ) (hm : 0 < m) :
    Nat.choose (2 * m) m = 2 * Nat.choose (2 * m - 1) m := by
  have hsymm :
      Nat.choose (2 * m - 1) (m - 1) = Nat.choose (2 * m - 1) m := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hpascal :
      Nat.choose (2 * m) m =
        Nat.choose (2 * m - 1) (m - 1) + Nat.choose (2 * m - 1) m := by
    have h := Nat.choose_succ_succ' (2 * m - 1) (m - 1)
    rw [show 2 * m - 1 + 1 = 2 * m by omega,
      show m - 1 + 1 = m by omega] at h
    exact h
  rw [hpascal, hsymm]
  omega

private theorem two_le_choose_pred_double (m : ℕ) (hm : 2 ≤ m) :
    2 ≤ Nat.choose (2 * m - 1) m := by
  have hmiddle : (2 * m - 1) / 2 = m - 1 := by omega
  have hsymm :
      Nat.choose (2 * m - 1) (m - 1) = Nat.choose (2 * m - 1) m := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hone := Nat.choose_le_middle 1 (2 * m - 1)
  rw [hmiddle, hsymm] at hone
  have hone' : 2 * m - 1 ≤ Nat.choose (2 * m - 1) m := by
    simpa using hone
  omega

/-- For `n ≥ 4`, the Tóth--Valtr threshold is strictly smaller than the
classical Erdős--Szekeres binomial threshold. -/
theorem tothValtr_strictly_improves_classical
    (n : ℕ) (hn : 4 ≤ n) :
    Nat.choose (2 * n - 5) (n - 2) + 2 <
      Nat.choose (2 * n - 4) (n - 2) + 1 := by
  let m := n - 2
  have hm : 2 ≤ m := by omega
  have hnsub : 2 * n - 5 = 2 * m - 1 := by omega
  have hncentral : 2 * n - 4 = 2 * m := by omega
  change Nat.choose (2 * n - 5) m + 2 < Nat.choose (2 * n - 4) m + 1
  rw [hnsub, hncentral, choose_double_eq_two_mul_choose_pred m (by omega)]
  have hchoose := two_le_choose_pred_double m hm
  omega

end ErdosSzekeres

end
