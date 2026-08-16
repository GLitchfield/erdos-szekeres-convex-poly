module

public import ErdosSzekeres.SukAdjacentRegions

@[expose] public section

/-!
# Cyclic support-cell contraction for a strict cap block

This file proves the local geometric contraction used by the normalized cyclic
Suk architecture.  A support cell cut out by four consecutive anchors is
contained in the support region cut out by every enclosing anchor block.  The
result is purely local: selecting the cyclic cut and producing the required
strict-cap order remain separate obligations.
-/

namespace ErdosSzekeres

noncomputable section

/-- A finite anchor sequence whose triples have the clockwise strict-cap sign. -/
def SukStrictCapSequence
    (n : ℕ) (anchors : ℕ → Point 2) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i < j → j < k → k < n →
    orientation (anchors i) (anchors j) (anchors k) < 0

/-- The rank-three Grassmann--Plücker identity for five affine points. -/
private theorem orientation_plucker (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

private theorem support_base_orientation_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (habp : orientation a b p < 0)
    (hcdp : orientation c d p < 0) :
    0 < orientation a d p := by
  have hpluckerC := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p, orientation_swap b c d] at hpluckerC
  have hcap : orientation c a p < 0 := by
    nlinarith
  have hacp : 0 < orientation a c p := by
    rw [orientation_swap a c p] at hcap
    linarith
  have hpluckerA := orientation_plucker a b c d p
  nlinarith

private theorem support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem support_left_diagonal_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : orientation b c p < 0)
    (hcdp : 0 < orientation c d p) :
    orientation a c p < 0 := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem support_right_diagonal_pos
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : 0 < orientation c d p)
    (hbcp : orientation b c p < 0) :
    0 < orientation c e p := by
  have hplucker := orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

private theorem support_right_diagonal_neg
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : orientation c d p < 0)
    (hbcp : 0 < orientation b c p) :
    orientation c e p < 0 := by
  have hplucker := orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

/-- Once the two support signs based at `b` are known, every earlier edge has
the negative support-side sign. -/
private theorem support_left_edge_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : orientation b c p < 0)
    (hbdp : 0 < orientation b d p) :
    orientation a b p < 0 := by
  have hplucker := orientation_plucker b a c d p
  rw [orientation_swap a b c, orientation_swap a b d,
    orientation_swap a b p] at hplucker
  nlinarith

/-- The reflected support signs force the negative side sign on every later
edge. -/
private theorem support_right_edge_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hacp : 0 < orientation a c p)
    (hbcp : orientation b c p < 0) :
    orientation c d p < 0 := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c, orientation_swap a c d,
    orientation_swap b c p, orientation_swap a c p,
    orientation_swap b c d] at hplucker
  nlinarith

theorem sukSupportRegion_subset_of_strictCapBlock
    (n a b c d i : ℕ) (anchors : ℕ → Point 2)
    (hcap : SukStrictCapSequence n anchors)
    (hab : a < b) (hbi : b ≤ i + 1)
    (hic : i + 2 ≤ c) (hcd : c < d) (hd : d < n) :
    SukSupportRegion
        (anchors i) (anchors (i + 1))
        (anchors (i + 2)) (anchors (i + 3)) ⊆
      SukSupportRegion
        (anchors a) (anchors b) (anchors c) (anchors d) := by
  intro p hp
  change 0 < orientation (anchors (i + 1)) (anchors (i + 2)) p ∧
    orientation (anchors i) (anchors (i + 1)) p < 0 ∧
    orientation (anchors (i + 2)) (anchors (i + 3)) p < 0 at hp
  rcases hp with ⟨hbase, hleft, hright⟩
  have hi1n : i + 1 < n := by omega
  have hi2n : i + 2 < n := by omega
  have hi3n : i + 3 < n := by omega

  have h_b_i1_neg (hb : b < i + 1) :
      orientation (anchors b) (anchors (i + 1)) p < 0 := by
    by_cases hbi' : b = i
    · subst b
      exact hleft
    · have hbiStrict : b < i := by omega
      exact support_left_diagonal_neg
        (anchors b) (anchors i) (anchors (i + 1)) (anchors (i + 2)) p
        (hcap hbiStrict (by omega) hi1n)
        (hcap (by omega) (by omega) hi2n)
        (hcap (by omega) (by omega) hi2n)
        hleft hbase

  have h_b_i2_pos (hb : b < i + 1) :
      0 < orientation (anchors b) (anchors (i + 2)) p := by
    exact support_left_diagonal_pos
      (anchors b) (anchors (i + 1)) (anchors (i + 2)) (anchors (i + 3)) p
      (hcap hb (by omega) hi2n)
      (hcap (by omega) (by omega) hi3n)
      (hcap (by omega) (by omega) hi3n)
      hbase hright

  have h_i2_c_neg (hc : i + 2 < c) :
      orientation (anchors (i + 2)) (anchors c) p < 0 := by
    by_cases hci3 : c = i + 3
    · subst c
      exact hright
    · have hi3c : i + 3 < c := by omega
      exact support_right_diagonal_neg
        (anchors (i + 1)) (anchors (i + 2)) (anchors (i + 3)) (anchors c) p
        (hcap (by omega) (by omega) hi3n)
        (hcap (by omega) (by omega) (by omega))
        (hcap (by omega) hi3c (by omega))
        hright hbase

  have h_i1_c_pos (hc : i + 2 < c) :
      0 < orientation (anchors (i + 1)) (anchors c) p := by
    exact support_right_diagonal_pos
      (anchors i) (anchors (i + 1)) (anchors (i + 2)) (anchors c) p
      (hcap (by omega) (by omega) hi2n)
      (hcap (by omega) (by omega) (by omega))
      (hcap (by omega) hc (by omega))
      hbase hleft

  have htargetLeft : orientation (anchors a) (anchors b) p < 0 := by
    by_cases hb : b = i + 1
    · subst b
      by_cases ha : a = i
      · subst a
        exact hleft
      · have hai : a < i := by omega
        exact support_left_diagonal_neg
          (anchors a) (anchors i) (anchors (i + 1)) (anchors (i + 2)) p
          (hcap hai (by omega) hi1n)
          (hcap (by omega) (by omega) hi2n)
          (hcap (by omega) (by omega) hi2n)
          hleft hbase
    · have hbStrict : b < i + 1 := by omega
      exact support_left_edge_neg
        (anchors a) (anchors b) (anchors (i + 1)) (anchors (i + 2)) p
        (hcap hab hbStrict hi1n)
        (hcap hab (by omega) hi2n)
        (hcap hbStrict (by omega) hi2n)
        (h_b_i1_neg hbStrict) (h_b_i2_pos hbStrict)

  have htargetRight : orientation (anchors c) (anchors d) p < 0 := by
    by_cases hc : c = i + 2
    · subst c
      by_cases hd' : d = i + 3
      · subst d
        exact hright
      · have hi3d : i + 3 < d := by omega
        exact support_right_diagonal_neg
          (anchors (i + 1)) (anchors (i + 2)) (anchors (i + 3)) (anchors d) p
          (hcap (by omega) (by omega) hi3n)
          (hcap (by omega) (by omega) (by omega))
          (hcap (by omega) hi3d hd)
          hright hbase
    · have hcStrict : i + 2 < c := by omega
      exact support_right_edge_neg
        (anchors (i + 1)) (anchors (i + 2)) (anchors c) (anchors d) p
        (hcap (by omega) hcStrict (by omega))
        (hcap (by omega) hcd hd)
        (hcap hcStrict hcd hd)
        (h_i1_c_pos hcStrict) (h_i2_c_neg hcStrict)

  have htargetBase : 0 < orientation (anchors b) (anchors c) p := by
    by_cases hb : b = i + 1
    · subst b
      by_cases hc : c = i + 2
      · subst c
        exact hbase
      · have hcStrict : i + 2 < c := by omega
        exact support_right_diagonal_pos
          (anchors i) (anchors (i + 1)) (anchors (i + 2)) (anchors c) p
          (hcap (by omega) (by omega) hi2n)
          (hcap (by omega) (by omega) (by omega))
          (hcap (by omega) hcStrict (by omega))
          hbase hleft
    · have hbStrict : b < i + 1 := by omega
      by_cases hc : c = i + 2
      · subst c
        exact support_left_diagonal_pos
          (anchors b) (anchors (i + 1)) (anchors (i + 2)) (anchors (i + 3)) p
          (hcap hbStrict (by omega) hi2n)
          (hcap (by omega) (by omega) hi3n)
          (hcap (by omega) (by omega) hi3n)
          hbase hright
      · have hcStrict : i + 2 < c := by omega
        exact support_base_orientation_pos
          (anchors b) (anchors (i + 1)) (anchors (i + 2)) (anchors c) p
          (hcap hbStrict (by omega) hi2n)
          (hcap hbStrict (by omega) (by omega))
          (hcap (by omega) hcStrict (by omega))
          (hcap (by omega) hcStrict (by omega))
          hbase (h_b_i1_neg hbStrict) (h_i2_c_neg hcStrict)

  exact ⟨htargetBase, htargetLeft, htargetRight⟩

end

end ErdosSzekeres
