module

public import ErdosSzekeres.SukPositiveFractionUpper
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# An explicit power bound for Suk's positive-fraction construction

The canonical scale is the least natural number whose cube covers the target
size.  Binomial symmetry is essential in the threshold comparison: it replaces
the antichain index `n - 2` by the complementary index `2 * K - 2` before the
standard power bound is applied.
-/

namespace ErdosSzekeres

noncomputable section

private theorem sukCubeScale_spec (n : Nat) :
    n ≤ sukCubeScale n ^ 3 := by
  unfold sukCubeScale
  exact Nat.find_spec (show Exists fun s : Nat ↦ n ≤ s ^ 3 from
    ⟨n, Nat.le_pow (by omega)⟩)

private theorem sukCubeScale_le_of_cube (n s : Nat) (h : n ≤ s ^ 3) :
    sukCubeScale n ≤ s := by
  unfold sukCubeScale
  exact Nat.find_min' (show Exists fun s : Nat ↦ n ≤ s ^ 3 from
    ⟨n, Nat.le_pow (by omega)⟩) h

private theorem sukCubeScale_five_le (n : Nat) (hn : 65 ≤ n) :
    5 ≤ sukCubeScale n := by
  by_contra h
  have hscale : sukCubeScale n ≤ 4 := by omega
  have hcube : sukCubeScale n ^ 3 ≤ 4 ^ 3 :=
    Nat.pow_le_pow_left hscale 3
  have hspec := sukCubeScale_spec n
  norm_num at hcube
  omega

private theorem sukCubeScale_pred_cube_lt (n : Nat) (hn : 65 ≤ n) :
    (sukCubeScale n - 1) ^ 3 < n := by
  have hs := sukCubeScale_five_le n hn
  by_contra h
  have hcandidate : n ≤ (sukCubeScale n - 1) ^ 3 := by omega
  have hminimal :=
    sukCubeScale_le_of_cube n (sukCubeScale n - 1) hcandidate
  omega

private theorem sukScale_sq_le_pred_cube (s : Nat) (hs : 5 ≤ s) :
    s ^ 2 ≤ (s - 1) ^ 3 := by
  have hsPred : 4 ≤ s - 1 := by omega
  have htail : 2 * (s - 1) + 1 ≤ (s - 1) * (s - 1) := by
    calc
      2 * (s - 1) + 1 ≤ 3 * (s - 1) := by omega
      _ ≤ (s - 1) * (s - 1) :=
        Nat.mul_le_mul_right (s - 1) (by omega)
  rw [show s = (s - 1) + 1 by omega]
  calc
    ((s - 1) + 1) ^ 2 =
        (s - 1) * (s - 1) + (2 * (s - 1) + 1) := by ring
    _ ≤ (s - 1) * (s - 1) + (s - 1) * (s - 1) :=
      Nat.add_le_add_left htail _
    _ = 2 * (s - 1) ^ 2 := by ring
    _ ≤ (s - 1) * (s - 1) ^ 2 :=
      Nat.mul_le_mul_right ((s - 1) ^ 2) (by omega)
    _ = (s - 1) ^ 3 := by ring

private theorem sukPoolLength_le_sq (s : Nat) :
    sukPoolLength s ≤ s ^ 2 := by
  have hfactor : 2 * sukSeparatedCount s - 1 ≤ s := by
    simp only [sukSeparatedCount, Nat.ceilDiv_eq_add_pred_div]
    omega
  rw [sukPoolLength]
  calc
    (2 * sukSeparatedCount s - 1) * s ≤ s * s :=
      Nat.mul_le_mul_right s hfactor
    _ = s ^ 2 := by ring

private theorem sukCarryWidth_le_sq
    (n s : Nat) (hs : 5 ≤ s) (hhigh : n ≤ s ^ 3) :
    sukCarryWidth n s ≤ s ^ 2 := by
  change n ⌈/⌉ s ≤ s ^ 2
  apply (ceilDiv_le_iff_le_mul
    (a := s) (b := n) (c := s ^ 2) (by omega)).2
  simpa [pow_succ, Nat.mul_comm] using hhigh

/-- The cube of the squared least scale is controlled by the square of `n`. -/
theorem sukCubeScale_sq_cube_le
    (n : Nat) (hn : 65 ≤ n) :
    (sukCubeScale n ^ 2) ^ 3 ≤ 64 * n ^ 2 := by
  let s := sukCubeScale n
  have hs : 5 ≤ s := by
    dsimp only [s]
    exact sukCubeScale_five_le n hn
  have hlow : (s - 1) ^ 3 < n := by
    dsimp only [s]
    exact sukCubeScale_pred_cube_lt n hn
  have hscale : s ≤ 2 * (s - 1) := by omega
  have hcube : s ^ 3 ≤ 8 * n := by
    calc
      s ^ 3 ≤ (2 * (s - 1)) ^ 3 := Nat.pow_le_pow_left hscale 3
      _ = 8 * (s - 1) ^ 3 := by ring
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 hlow.le
  change (s ^ 2) ^ 3 ≤ 64 * n ^ 2
  calc
    (s ^ 2) ^ 3 = (s ^ 3) ^ 2 := by ring
    _ ≤ (8 * n) ^ 2 := Nat.pow_le_pow_left hcube 2
    _ = 64 * n ^ 2 := by ring

private theorem sukPositiveFractionThreshold_le_explicitPower
    (n s : Nat)
    (hn : 65 ≤ n)
    (hs : 5 ≤ s)
    (hlow : (s - 1) ^ 3 < n)
    (hhigh : n ≤ s ^ 3) :
    sukPositiveFractionThreshold n s ≤
      2 ^ (n + 64 * s ^ 2 * Nat.clog 2 (3 * n) + 128) := by
  let L := sukPoolLength s
  let K := sukCarryWidth n s
  let c := Nat.clog 2 (3 * n)
  let z := s ^ 2 * c
  let x := n + K - 4
  have hL : L ≤ s ^ 2 := by
    dsimp only [L]
    exact sukPoolLength_le_sq s
  have hK : K ≤ s ^ 2 := by
    dsimp only [K]
    exact sukCarryWidth_le_sq n s hs hhigh
  have hcarryCover : n ≤ s * K := by
    dsimp only [K]
    change n ≤ s * (n ⌈/⌉ s)
    exact (ceilDiv_le_iff_le_mul
      (a := s) (b := n) (c := n ⌈/⌉ s) (by omega)).1 le_rfl
  have hKpos : 1 ≤ K := by
    by_contra h
    have hzero : K = 0 := by omega
    rw [hzero, Nat.mul_zero] at hcarryCover
    omega
  have hsqLt : s ^ 2 < n :=
    (sukScale_sq_le_pred_cube s hs).trans_lt hlow
  have hKn : K ≤ n := hK.trans hsqLt.le
  have hlog : 1 ≤ c := by
    dsimp only [c]
    have := Nat.clog_pos (b := 2) (n := 3 * n) (by norm_num) (by omega)
    omega
  have hsz : s ^ 2 ≤ z := by
    dsimp only [z]
    calc
      s ^ 2 = s ^ 2 * 1 := by simp
      _ ≤ s ^ 2 * c := Nat.mul_le_mul_left (s ^ 2) hlog
  have hKlog : 2 * K * c ≤ 2 * z := by
    dsimp only [z]
    calc
      2 * K * c ≤ 2 * s ^ 2 * c :=
        Nat.mul_le_mul_right c (Nat.mul_le_mul_left 2 hK)
      _ = 2 * (s ^ 2 * c) := by ring
  have hclogCover : 3 * n ≤ 2 ^ c := by
    dsimp only [c]
    exact (Nat.clog_le_iff_le_pow (by norm_num)).1 le_rfl
  have htopSplit :
      n + 2 * K - 4 = (n - 2) + (2 * K - 2) := by
    omega
  have htop : n + 2 * K - 4 ≤ 3 * n := by omega
  have hchooseSymm :
      Nat.choose (n + 2 * K - 4) (n - 2) =
        Nat.choose (n + 2 * K - 4) (2 * K - 2) :=
    Nat.choose_symm_of_eq_add htopSplit
  have hcomplementExponent : c * (2 * K - 2) ≤ 2 * K * c := by
    have h := Nat.mul_le_mul_left c (Nat.sub_le (2 * K) 2)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hchoose :
      Nat.choose (n + 2 * K - 4) (n - 2) ≤ 2 ^ (2 * K * c) := by
    calc
      Nat.choose (n + 2 * K - 4) (n - 2) =
          Nat.choose (n + 2 * K - 4) (2 * K - 2) := hchooseSymm
      _ ≤ (n + 2 * K - 4) ^ (2 * K - 2) := Nat.choose_le_pow _ _
      _ ≤ (3 * n) ^ (2 * K - 2) :=
        Nat.pow_le_pow_left htop (2 * K - 2)
      _ ≤ (2 ^ c) ^ (2 * K - 2) :=
        Nat.pow_le_pow_left hclogCover (2 * K - 2)
      _ = 2 ^ (c * (2 * K - 2)) := by rw [pow_mul]
      _ ≤ 2 ^ (2 * K * c) :=
        Nat.pow_le_pow_right (by norm_num) hcomplementExponent
  have hinner :
      2 ^ x * Nat.choose (n + 2 * K - 4) (n - 2) + 1 ≤
        2 ^ (x + 2 * K * c + 1) := by
    calc
      2 ^ x * Nat.choose (n + 2 * K - 4) (n - 2) + 1 ≤
          2 ^ x * 2 ^ (2 * K * c) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (2 ^ x) hchoose) 1
      _ = 2 ^ (x + 2 * K * c) + 1 := by rw [pow_add]
      _ ≤ 2 ^ (x + 2 * K * c + 1) := by
        rw [pow_succ]
        have hpow : 1 ≤ 2 ^ (x + 2 * K * c) := Nat.one_le_two_pow
        omega
  have hfortyL : 40 * L ≤ 40 * s ^ 2 := Nat.mul_le_mul_left 40 hL
  have hx : x ≤ n + K := by
    dsimp only [x]
    omega
  have hcoarseCrude :
      40 * L + (x + 2 * K * c + 1) ≤
        n + 41 * s ^ 2 + 2 * z + 1 := by
    omega
  have hfortyOne : 41 * s ^ 2 ≤ 41 * z := Nat.mul_le_mul_left 41 hsz
  have hcoarseExponent :
      40 * L + (x + 2 * K * c + 1) ≤
        n + 64 * s ^ 2 * c + 128 := by
    calc
      40 * L + (x + 2 * K * c + 1) ≤
          n + 41 * s ^ 2 + 2 * z + 1 := hcoarseCrude
      _ ≤ n + 64 * z + 128 := by omega
      _ = n + 64 * s ^ 2 * c + 128 := by
        dsimp only [z]
        ring
  have hthirtyTwoL :
      32 * (L + 3) + 1 ≤ 32 * (s ^ 2 + 3) + 1 :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hL 3)) 1
  have hthirtyTwo : 32 * s ^ 2 ≤ 32 * z := Nat.mul_le_mul_left 32 hsz
  have hfineExponent :
      32 * (L + 3) + 1 ≤ n + 64 * s ^ 2 * c + 128 := by
    calc
      32 * (L + 3) + 1 ≤ 32 * (s ^ 2 + 3) + 1 := hthirtyTwoL
      _ ≤ n + 64 * z + 128 := by omega
      _ = n + 64 * s ^ 2 * c + 128 := by
        dsimp only [z]
        ring
  change max
      (2 * porValtrFineDenominator L)
      (sukCoarseDenominator L *
        ((sukChainThreshold n s - 1) *
          (sukAntichainThreshold n s - 1) + 1)) ≤
    2 ^ (n + 64 * s ^ 2 * c + 128)
  apply max_le
  · calc
      2 * porValtrFineDenominator L = 2 ^ (32 * (L + 3) + 1) := by
        simp [porValtrFineDenominator, pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ (n + 64 * s ^ 2 * c + 128) :=
        Nat.pow_le_pow_right (by norm_num) hfineExponent
  · calc
      sukCoarseDenominator L *
          ((sukChainThreshold n s - 1) *
            (sukAntichainThreshold n s - 1) + 1) =
          2 ^ (40 * L) *
            (2 ^ x * Nat.choose (n + 2 * K - 4) (n - 2) + 1) := by
        simp [sukCoarseDenominator, sukChainThreshold,
          sukAntichainThreshold, sukLocalCapSize, K, x]
      _ ≤ 2 ^ (40 * L) * 2 ^ (x + 2 * K * c + 1) :=
        Nat.mul_le_mul_left (2 ^ (40 * L)) hinner
      _ = 2 ^ (40 * L + (x + 2 * K * c + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ (n + 64 * s ^ 2 * c + 128) :=
        Nat.pow_le_pow_right (by norm_num) hcoarseExponent

/-- The frozen positive-fraction threshold is bounded by one explicit power. -/
theorem suk_explicit_upper
    (n : Nat) (hn : 65 ≤ n) :
    ForcesConvexPolygon n
      (2 ^ (n + 64 * sukCubeScale n ^ 2 *
        Nat.clog 2 (3 * n) + 128)) := by
  let s := sukCubeScale n
  have hs : 5 ≤ s := by
    dsimp only [s]
    exact sukCubeScale_five_le n hn
  have hlow : (s - 1) ^ 3 < n := by
    dsimp only [s]
    exact sukCubeScale_pred_cube_lt n hn
  have hhigh : n ≤ s ^ 3 := by
    dsimp only [s]
    exact sukCubeScale_spec n
  have hthreshold :=
    sukPositiveFractionThreshold_le_explicitPower n s hn hs hlow hhigh
  have hforces := sukPositiveFraction_forces_threshold n s hs hlow hhigh
  change ForcesConvexPolygon n
    (2 ^ (n + 64 * s ^ 2 * Nat.clog 2 (3 * n) + 128))
  intro P hcard hgeneral
  exact hforces P (hthreshold.trans hcard) hgeneral

end

end ErdosSzekeres

end
