module

public import ErdosSzekeres.Sweep

@[expose] public section

/-!
# Rank-three brackets and alternating signs

This file supplies the geometric bridge needed by finite nonrealizability
certificates.  A planar point is homogenized to a vector in `ℝ³`; its
three-vector bracket is exactly the planar orientation determinant.
-/

namespace ErdosSzekeres

noncomputable section

/-- A homogeneous rank-three vector. -/
abbrev RankThreeVector := Fin 3 → ℝ

/-- The determinant of the matrix whose rows are the three supplied vectors. -/
def rankThreeBracket (u v w : RankThreeVector) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0)

@[simp] theorem rankThreeBracket_smul
    (a b c : ℝ) (u v w : RankThreeVector) :
    rankThreeBracket (a • u) (b • v) (c • w) =
      a * b * c * rankThreeBracket u v w := by
  simp only [rankThreeBracket, Pi.smul_apply, smul_eq_mul]
  ring

theorem rankThreeBracket_swap_first (u v w : RankThreeVector) :
    rankThreeBracket v u w = -rankThreeBracket u v w := by
  simp only [rankThreeBracket]
  ring

theorem rankThreeBracket_swap_last (u v w : RankThreeVector) :
    rankThreeBracket u w v = -rankThreeBracket u v w := by
  simp only [rankThreeBracket]
  ring

theorem rankThreeBracket_rotate (u v w : RankThreeVector) :
    rankThreeBracket v w u = rankThreeBracket u v w := by
  simp only [rankThreeBracket]
  ring

/-- The rank-three Grassmann--Plücker relation with one common vector. -/
theorem rankThreeBracket_plucker
    (a b c d e : RankThreeVector) :
    rankThreeBracket a b c * rankThreeBracket a d e -
        rankThreeBracket a b d * rankThreeBracket a c e +
      rankThreeBracket a b e * rankThreeBracket a c d = 0 := by
  simp only [rankThreeBracket]
  ring

/-- The affine point `(x,y)` regarded as the homogeneous vector `(x,y,1)`. -/
def homogenize (p : Point 2) : RankThreeVector := ![p 0, p 1, 1]

@[simp] theorem rankThreeBracket_homogenize (a b c : Point 2) :
    rankThreeBracket (homogenize a) (homogenize b) (homogenize c) =
      orientation a b c := by
  simp only [rankThreeBracket, homogenize, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, orientation]
  ring

/-- The numeric sign attached to a left or right turn. -/
def Turn.realSign : Turn → ℝ
  | .left => 1
  | .right => -1

@[simp] theorem Turn.realSign_left : Turn.left.realSign = 1 := rfl

@[simp] theorem Turn.realSign_right : Turn.right.realSign = -1 := rfl

/-- Extend an increasing-triple coloring to an alternating sign function on
all ordered triples.  Repeated arguments receive sign zero. -/
def TripleColoring.alternatingSign {n : ℕ} (chi : TripleColoring n)
    (a b c : Fin n) : ℝ :=
  if hab : a = b then 0
  else if hac : a = c then 0
  else if hbc : b = c then 0
  else if hablt : a < b then
    if hbclt : b < c then
      (chi ⟨a, b, c, hablt, hbclt⟩).realSign
    else if haclt : a < c then
      -(chi ⟨a, c, b, haclt, by omega⟩).realSign
    else
      (chi ⟨c, a, b, by omega, hablt⟩).realSign
  else if haclt : a < c then
    -(chi ⟨b, a, c, by omega, haclt⟩).realSign
  else if hbclt : b < c then
    (chi ⟨b, c, a, hbclt, by omega⟩).realSign
  else
    -(chi ⟨c, b, a, by omega, by omega⟩).realSign

@[simp] theorem TripleColoring.alternatingSign_orderedTriple {n : ℕ}
    (chi : TripleColoring n) (t : OrderedTriple n) :
    chi.alternatingSign t.i t.j t.k = (chi t).realSign := by
  simp [TripleColoring.alternatingSign, ne_of_lt t.hij,
    ne_of_lt (t.hij.trans t.hjk), ne_of_lt t.hjk, t.hij, t.hjk]

/-- A vector family realizes an alternating sign function when every distinct
triple has the prescribed strict bracket sign. -/
def RankThreeVectorRealizes {n : ℕ}
    (sigma : Fin n → Fin n → Fin n → ℝ)
    (v : Fin n → RankThreeVector) : Prop :=
  ∀ ⦃i j k⦄, i ≠ j → i ≠ k → j ≠ k →
    0 < sigma i j k * rankThreeBracket (v i) (v j) (v k)

/-- A bracket normalized by its prescribed alternating sign. -/
def normalizedRankThreeBracket {n : ℕ}
    (sigma : Fin n → Fin n → Fin n → ℝ)
    (v : Fin n → RankThreeVector) (i j k : Fin n) : ℝ :=
  sigma i j k * rankThreeBracket (v i) (v j) (v k)

/-- Every normalized bracket of a realized distinct triple is positive. -/
theorem RankThreeVectorRealizes.normalizedBracket_pos {n : ℕ}
    {sigma : Fin n → Fin n → Fin n → ℝ}
    {v : Fin n → RankThreeVector} (h : RankThreeVectorRealizes sigma v)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 < normalizedRankThreeBracket sigma v i j k :=
  h hij hik hjk

/-- Realizability by nonzero homogeneous rank-three vectors. -/
def RankThreeVectorRealizable {n : ℕ}
    (sigma : Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ v : Fin n → RankThreeVector, RankThreeVectorRealizes sigma v

/-- A scalar sign used in a reorientation or a global chirotope reversal. -/
def IsRealSign (x : ℝ) : Prop := x = 1 ∨ x = -1

/-- Full rank-three reorientation equivalence: arbitrary relabeling, one sign
per element, and an independent global sign. -/
def RankThreeReorientationEquivalent {n : ℕ}
    (sigma tau : Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ p : Equiv.Perm (Fin n), ∃ epsilon : Fin n → ℝ, ∃ delta : ℝ,
    (∀ i, IsRealSign (epsilon i)) ∧ IsRealSign delta ∧
      ∀ i j k,
        sigma i j k =
          delta * epsilon i * epsilon j * epsilon k *
            tau (p i) (p j) (p k)

/-- Reorientation and relabeling preserve vector realizability. -/
theorem RankThreeVectorRealizable.of_reorientationEquivalent {n : ℕ}
    {sigma tau : Fin n → Fin n → Fin n → ℝ}
    (hsigma : RankThreeVectorRealizable sigma)
    (hequiv : RankThreeReorientationEquivalent sigma tau) :
    RankThreeVectorRealizable tau := by
  obtain ⟨v, hv⟩ := hsigma
  obtain ⟨p, epsilon, delta, _hepsilon, hdelta, hequiv⟩ := hequiv
  let w : Fin n → RankThreeVector := fun q =>
    (delta * epsilon (p.symm q)) • v (p.symm q)
  refine ⟨w, ?_⟩
  intro i j k hij hik hjk
  have hsource := hv (p.symm.injective.ne hij)
    (p.symm.injective.ne hik) (p.symm.injective.ne hjk)
  have htransport := hequiv (p.symm i) (p.symm j) (p.symm k)
  simp only [p.apply_symm_apply] at htransport
  have heq :
      tau i j k * rankThreeBracket (w i) (w j) (w k) =
        sigma (p.symm i) (p.symm j) (p.symm k) *
          rankThreeBracket (v (p.symm i)) (v (p.symm j)) (v (p.symm k)) := by
    simp only [w, rankThreeBracket_smul]
    rw [htransport]
    rcases hdelta with rfl | rfl <;> norm_num <;> ring
  rw [heq]
  exact hsource

/-- On an increasing triple, homogenized sweep points have the sign recorded
by the induced coloring. -/
theorem SweptConfiguration.ordered_sign_mul_bracket_pos {n : ℕ}
    (P : SweptConfiguration n) (t : OrderedTriple n) :
    0 < (P.tripleColoring t).realSign *
      rankThreeBracket (homogenize (P.point t.i))
        (homogenize (P.point t.j)) (homogenize (P.point t.k)) := by
  rw [rankThreeBracket_homogenize]
  cases hturn : P.tripleColoring t with
  | left =>
      simp only [Turn.realSign_left, one_mul]
      exact (P.turn_eq_left_iff t.i t.j t.k).mp hturn
  | right =>
      simp only [Turn.realSign_right, neg_mul, one_mul]
      have hneg := (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).mp hturn
      linarith

/-- The homogeneous vectors of a swept planar configuration realize the full
alternating sign extension of its increasing-triple coloring. -/
theorem SweptConfiguration.alternatingSign_rankThreeVectorRealizable {n : ℕ}
    (P : SweptConfiguration n) :
    RankThreeVectorRealizable P.tripleColoring.alternatingSign := by
  refine ⟨fun i => homogenize (P.point i), ?_⟩
  intro i j k hij hik hjk
  by_cases hijlt : i < j
  · by_cases hjklt : j < k
    · have h := P.ordered_sign_mul_bracket_pos ⟨i, j, k, hijlt, hjklt⟩
      simpa [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
        hjklt] using h
    · by_cases hiklt : i < k
      · have hkj : k < j := by omega
        have h := P.ordered_sign_mul_bracket_pos ⟨i, k, j, hiklt, hkj⟩
        have hsign :
            P.tripleColoring.alternatingSign i j k =
              -(P.tripleColoring ⟨i, k, j, hiklt, hkj⟩).realSign := by
          simp [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
            hjklt, hiklt]
        have hbracket :
            rankThreeBracket (homogenize (P.point i))
                (homogenize (P.point j)) (homogenize (P.point k)) =
              -rankThreeBracket (homogenize (P.point i))
                (homogenize (P.point k)) (homogenize (P.point j)) :=
          rankThreeBracket_swap_last _ _ _
        rw [hsign, hbracket]
        simpa only [neg_mul_neg] using h
      · have hki : k < i := by omega
        have h := P.ordered_sign_mul_bracket_pos ⟨k, i, j, hki, hijlt⟩
        have hsign :
            P.tripleColoring.alternatingSign i j k =
              (P.tripleColoring ⟨k, i, j, hki, hijlt⟩).realSign := by
          simp [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
            hjklt, hiklt]
        have hbracket :
            rankThreeBracket (homogenize (P.point i))
                (homogenize (P.point j)) (homogenize (P.point k)) =
              rankThreeBracket (homogenize (P.point k))
                (homogenize (P.point i)) (homogenize (P.point j)) := by
          rw [rankThreeBracket_rotate]
        rw [hsign, hbracket]
        exact h
  · have hjilt : j < i := by omega
    by_cases hiklt : i < k
    · have h := P.ordered_sign_mul_bracket_pos ⟨j, i, k, hjilt, hiklt⟩
      have hsign :
          P.tripleColoring.alternatingSign i j k =
            -(P.tripleColoring ⟨j, i, k, hjilt, hiklt⟩).realSign := by
        simp [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
          hiklt]
      have hbracket :
          rankThreeBracket (homogenize (P.point i))
              (homogenize (P.point j)) (homogenize (P.point k)) =
            -rankThreeBracket (homogenize (P.point j))
              (homogenize (P.point i)) (homogenize (P.point k)) :=
        rankThreeBracket_swap_first _ _ _
      rw [hsign, hbracket]
      simpa only [neg_mul_neg] using h
    · have hki : k < i := by omega
      by_cases hjklt : j < k
      · have h := P.ordered_sign_mul_bracket_pos ⟨j, k, i, hjklt, hki⟩
        have hsign :
            P.tripleColoring.alternatingSign i j k =
              (P.tripleColoring ⟨j, k, i, hjklt, hki⟩).realSign := by
          simp [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
            hiklt, hjklt]
        have hbracket :
            rankThreeBracket (homogenize (P.point i))
                (homogenize (P.point j)) (homogenize (P.point k)) =
              rankThreeBracket (homogenize (P.point j))
                (homogenize (P.point k)) (homogenize (P.point i)) := by
          exact (rankThreeBracket_rotate _ _ _).symm
        rw [hsign, hbracket]
        exact h
      · have hkj : k < j := by omega
        have h := P.ordered_sign_mul_bracket_pos ⟨k, j, i, hkj, hjilt⟩
        have hsign :
            P.tripleColoring.alternatingSign i j k =
              -(P.tripleColoring ⟨k, j, i, hkj, hjilt⟩).realSign := by
          simp [TripleColoring.alternatingSign, hij, hik, hjk, hijlt,
            hiklt, hjklt]
        have hbracket :
            rankThreeBracket (homogenize (P.point i))
                (homogenize (P.point j)) (homogenize (P.point k)) =
              -rankThreeBracket (homogenize (P.point k))
                (homogenize (P.point j)) (homogenize (P.point i)) := by
          simp only [rankThreeBracket]
          ring
        rw [hsign, hbracket]
        simpa only [neg_mul_neg] using h

/-- Every sweep-realizable coloring has a homogeneous rank-three vector
realization of its alternating sign extension. -/
theorem IsSweepRealizable.rankThreeVectorRealizable {n : ℕ}
    {chi : TripleColoring n} (hchi : IsSweepRealizable chi) :
    RankThreeVectorRealizable chi.alternatingSign := by
  obtain ⟨P, rfl⟩ := hchi
  exact P.alternatingSign_rankThreeVectorRealizable

end
end ErdosSzekeres

end
