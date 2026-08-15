module

public import ErdosSzekeres.DecomposableRealization
public import ErdosSzekeres.RingelNine

@[expose] public section

/-!
# Ringel-nine exclusion for geometric and decomposable colorings

The certificate-backed nonrealizability theorem is added at the bottom of this
module once its exact finite certificate has passed two independent checkers.
The lemmas above that boundary are generic geometric transport.
-/

namespace ErdosSzekeres

noncomputable section

/-- A fixed-abscissa realization on a subset induces a swept realization on
any increasingly enumerated subfamily of that subset. -/
theorem FixedXRealizesOn.restrict_isSweepRealizable {m n : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)} {y : Fin n → ℝ}
    (hrealizes : FixedXRealizesOn chi s y) (f : Fin m ↪o Fin n)
    (hf : ∀ i, f i ∈ s) :
    IsSweepRealizable (chi.restrict f) := by
  let P : SweptConfiguration m :=
    { point := fun i => ordinatePoint y (f i)
      sweep_strictMono := by
        intro i j hij
        simp only [ordinatePoint_zero]
        exact_mod_cast f.strictMono hij
      generalPosition := by
        apply generalPosition_of_ordered
        intro i j k hij hjk
        let t : OrderedTriple n :=
          ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩
        have hsign := hrealizes t (hf i) (hf j) (hf k)
        cases hcolor : chi t with
        | left =>
            have hpos :
                0 < orientation (ordinatePoint y (f i))
                  (ordinatePoint y (f j)) (ordinatePoint y (f k)) := by
              simpa [t, hcolor, RealizesTurn] using hsign
            exact ne_of_gt hpos
        | right =>
            have hneg :
                orientation (ordinatePoint y (f i))
                    (ordinatePoint y (f j)) (ordinatePoint y (f k)) < 0 := by
              simpa [t, hcolor, RealizesTurn] using hsign
            exact ne_of_lt hneg }
  refine ⟨P, ?_⟩
  funext t
  change P.turn t.i t.j t.k = chi (t.map f)
  have hsign := hrealizes (t.map f) (hf t.i) (hf t.j) (hf t.k)
  cases hcolor : chi (t.map f) with
  | left =>
      apply (P.turn_eq_left_iff t.i t.j t.k).mpr
      simpa [P, hcolor, RealizesTurn] using hsign
  | right =>
      apply (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).mpr
      simpa [P, hcolor, RealizesTurn] using hsign

/-- Recursive decomposability on a carrier gives a swept realization on every
increasingly selected subfamily of that carrier. -/
theorem IsDecomposableOn.restrict_isSweepRealizable {m n : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)}
    (hdecomp : IsDecomposableOn chi s) (f : Fin m ↪o Fin n)
    (hf : ∀ i, f i ∈ s) :
    IsSweepRealizable (chi.restrict f) := by
  obtain ⟨y, hy⟩ := hdecomp.exists_fixedXRealization
  exact hy.restrict_isSweepRealizable f hf

/-- Conditional decomposable-carrier exclusion, before importing the exact
Ringel nonrealizability certificate. -/
theorem IsDecomposableOn.noRingelNineRestrictionOn_of_nonrealizable {n : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)}
    (hdecomp : IsDecomposableOn chi s)
    (hRingel : ¬RankThreeVectorRealizable ringelNineChirotope)
    (f : Fin 9 ↪o Fin n) (hf : ∀ i, f i ∈ s) :
    ¬HasRingelNineRestrictionOn chi f := by
  intro hrestriction
  have hrestricted := hdecomp.restrict_isSweepRealizable f hf
  exact hRingel
    (hrestricted.rankThreeVectorRealizable.of_reorientationEquivalent
      hrestriction)

-- BEGIN GENERATED RINGEL-NINE CERTIFICATE

namespace RingelNine

/-- The positive normalized magnitude of an increasing Ringel bracket. -/
def magnitude (v : Fin 9 → RankThreeVector) (i j k : Fin 9) : ℝ :=
  normalizedRankThreeBracket ringelNineChirotope v i j k

@[simp] theorem chirotope_0_1_2 :
    ringelNineChirotope 0 1 2 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_3 :
    ringelNineChirotope 0 1 3 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_4 :
    ringelNineChirotope 0 1 4 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_5 :
    ringelNineChirotope 0 1 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_6 :
    ringelNineChirotope 0 1 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_7 :
    ringelNineChirotope 0 1 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_1_8 :
    ringelNineChirotope 0 1 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_3 :
    ringelNineChirotope 0 2 3 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_4 :
    ringelNineChirotope 0 2 4 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_5 :
    ringelNineChirotope 0 2 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_6 :
    ringelNineChirotope 0 2 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_7 :
    ringelNineChirotope 0 2 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_2_8 :
    ringelNineChirotope 0 2 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_3_4 :
    ringelNineChirotope 0 3 4 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_3_5 :
    ringelNineChirotope 0 3 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_3_6 :
    ringelNineChirotope 0 3 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_3_7 :
    ringelNineChirotope 0 3 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_3_8 :
    ringelNineChirotope 0 3 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_4_5 :
    ringelNineChirotope 0 4 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_4_6 :
    ringelNineChirotope 0 4 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_4_7 :
    ringelNineChirotope 0 4 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_4_8 :
    ringelNineChirotope 0 4 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_5_6 :
    ringelNineChirotope 0 5 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_5_7 :
    ringelNineChirotope 0 5 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_5_8 :
    ringelNineChirotope 0 5 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_6_7 :
    ringelNineChirotope 0 6 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_6_8 :
    ringelNineChirotope 0 6 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_0_7_8 :
    ringelNineChirotope 0 7 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_2_3 :
    ringelNineChirotope 1 2 3 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_2_4 :
    ringelNineChirotope 1 2 4 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_2_5 :
    ringelNineChirotope 1 2 5 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_2_6 :
    ringelNineChirotope 1 2 6 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_2_7 :
    ringelNineChirotope 1 2 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_2_8 :
    ringelNineChirotope 1 2 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_3_4 :
    ringelNineChirotope 1 3 4 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_3_5 :
    ringelNineChirotope 1 3 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_3_6 :
    ringelNineChirotope 1 3 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_3_7 :
    ringelNineChirotope 1 3 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_3_8 :
    ringelNineChirotope 1 3 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_4_5 :
    ringelNineChirotope 1 4 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_4_6 :
    ringelNineChirotope 1 4 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_4_7 :
    ringelNineChirotope 1 4 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_4_8 :
    ringelNineChirotope 1 4 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_5_6 :
    ringelNineChirotope 1 5 6 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_5_7 :
    ringelNineChirotope 1 5 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_5_8 :
    ringelNineChirotope 1 5 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_1_6_7 :
    ringelNineChirotope 1 6 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_6_8 :
    ringelNineChirotope 1 6 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_1_7_8 :
    ringelNineChirotope 1 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_2_3_4 :
    ringelNineChirotope 2 3 4 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_3_5 :
    ringelNineChirotope 2 3 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_3_6 :
    ringelNineChirotope 2 3 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_3_7 :
    ringelNineChirotope 2 3 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_3_8 :
    ringelNineChirotope 2 3 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_4_5 :
    ringelNineChirotope 2 4 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_4_6 :
    ringelNineChirotope 2 4 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_4_7 :
    ringelNineChirotope 2 4 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_4_8 :
    ringelNineChirotope 2 4 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_5_6 :
    ringelNineChirotope 2 5 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_5_7 :
    ringelNineChirotope 2 5 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_5_8 :
    ringelNineChirotope 2 5 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_6_7 :
    ringelNineChirotope 2 6 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_6_8 :
    ringelNineChirotope 2 6 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_2_7_8 :
    ringelNineChirotope 2 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_3_4_5 :
    ringelNineChirotope 3 4 5 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_4_6 :
    ringelNineChirotope 3 4 6 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_4_7 :
    ringelNineChirotope 3 4 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_4_8 :
    ringelNineChirotope 3 4 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_5_6 :
    ringelNineChirotope 3 5 6 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_3_5_7 :
    ringelNineChirotope 3 5 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_5_8 :
    ringelNineChirotope 3 5 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_3_6_7 :
    ringelNineChirotope 3 6 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_6_8 :
    ringelNineChirotope 3 6 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_3_7_8 :
    ringelNineChirotope 3 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_5_6 :
    ringelNineChirotope 4 5 6 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_5_7 :
    ringelNineChirotope 4 5 7 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_5_8 :
    ringelNineChirotope 4 5 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_6_7 :
    ringelNineChirotope 4 6 7 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_6_8 :
    ringelNineChirotope 4 6 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_4_7_8 :
    ringelNineChirotope 4 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_5_6_7 :
    ringelNineChirotope 5 6 7 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_5_6_8 :
    ringelNineChirotope 5 6 8 =
      1 := by
  change (1 : ℝ) = 1
  rfl

@[simp] theorem chirotope_5_7_8 :
    ringelNineChirotope 5 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

@[simp] theorem chirotope_6_7_8 :
    ringelNineChirotope 6 7 8 =
      -1 := by
  change (-1 : ℝ) = -1
  rfl

end RingelNine

private theorem row_00 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 8 *
        RingelNine.magnitude v 0 6 7 <
      RingelNine.magnitude v 0 2 7 *
        RingelNine.magnitude v 0 6 8 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 2) (v 6) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_6,
    RingelNine.chirotope_0_2_7,
    RingelNine.chirotope_0_2_8,
    RingelNine.chirotope_0_6_7,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_01 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 6 *
        RingelNine.magnitude v 0 3 4 <
      RingelNine.magnitude v 0 2 4 *
        RingelNine.magnitude v 0 3 6 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 2) (v 3) (v 4) (v 6)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 4 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_2_4,
    RingelNine.chirotope_0_2_6,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_3_6,
    RingelNine.chirotope_0_4_6,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_02 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 4 *
        RingelNine.magnitude v 0 5 8 <
      RingelNine.magnitude v 0 1 5 *
        RingelNine.magnitude v 0 4 8 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 1) (v 4) (v 5) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_4,
    RingelNine.chirotope_0_1_5,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_0_4_8,
    RingelNine.chirotope_0_5_8,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_03 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 0 4 7 <
      RingelNine.magnitude v 0 1 7 *
        RingelNine.magnitude v 0 4 8 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 1) (v 4) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_4,
    RingelNine.chirotope_0_1_7,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_4_7,
    RingelNine.chirotope_0_4_8,
    RingelNine.chirotope_0_7_8,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_04 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 0 5 7 <
      RingelNine.magnitude v 0 1 7 *
        RingelNine.magnitude v 0 5 8 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 1) (v 5) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_5,
    RingelNine.chirotope_0_1_7,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_5_7,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_7_8,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_05 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 4 7 *
        RingelNine.magnitude v 0 5 6 <
      RingelNine.magnitude v 0 4 6 *
        RingelNine.magnitude v 0 5 7 := by
  have hgp := rankThreeBracket_plucker (v 0) (v 4) (v 5) (v 6) (v 7)
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 0 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_0_4_6,
    RingelNine.chirotope_0_4_7,
    RingelNine.chirotope_0_5_6,
    RingelNine.chirotope_0_5_7,
    RingelNine.chirotope_0_6_7,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_06 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 2 *
        RingelNine.magnitude v 2 3 4 <
      RingelNine.magnitude v 0 2 4 *
        RingelNine.magnitude v 1 2 3 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 0) (v 1) (v 3) (v 4)
  have hperm_0 :
      rankThreeBracket (v 2) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 2) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 0) (v 3) =
        -rankThreeBracket (v 0) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 2) (v 1) (v 4) =
        -rankThreeBracket (v 1) (v 2) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 0) (v 4) =
        -rankThreeBracket (v 0) (v 2) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 2) (v 1) (v 3) =
        -rankThreeBracket (v 1) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 2 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_2,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_2_4,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_2_4,
    RingelNine.chirotope_2_3_4,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_07 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 2 *
        RingelNine.magnitude v 2 3 5 <
      RingelNine.magnitude v 0 2 5 *
        RingelNine.magnitude v 1 2 3 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 0) (v 1) (v 3) (v 5)
  have hperm_0 :
      rankThreeBracket (v 2) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 2) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 0) (v 3) =
        -rankThreeBracket (v 0) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 2) (v 1) (v 5) =
        -rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 2) (v 1) (v 3) =
        -rankThreeBracket (v 1) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 2 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_2,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_2_5,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_2_3_5,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_08 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 7 *
        RingelNine.magnitude v 2 3 6 <
      RingelNine.magnitude v 0 2 6 *
        RingelNine.magnitude v 2 3 7 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 0) (v 3) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 2) (v 0) (v 3) =
        -rankThreeBracket (v 0) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 0) (v 6) =
        -rankThreeBracket (v 0) (v 2) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 2) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_2_6,
    RingelNine.chirotope_0_2_7,
    RingelNine.chirotope_2_3_6,
    RingelNine.chirotope_2_3_7,
    RingelNine.chirotope_2_6_7,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_09 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 2 6 8 <
      RingelNine.magnitude v 1 2 6 *
        RingelNine.magnitude v 2 5 8 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 1) (v 5) (v 6) (v 8)
  have hperm_0 :
      rankThreeBracket (v 2) (v 1) (v 5) =
        -rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 1) (v 6) =
        -rankThreeBracket (v 1) (v 2) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 2) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_2_5_6,
    RingelNine.chirotope_2_5_8,
    RingelNine.chirotope_2_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_10 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 2 6 8 <
      RingelNine.magnitude v 1 2 6 *
        RingelNine.magnitude v 2 5 8 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 1) (v 5) (v 6) (v 8)
  have hperm_0 :
      rankThreeBracket (v 2) (v 1) (v 5) =
        -rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 1) (v 6) =
        -rankThreeBracket (v 1) (v 2) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 2) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_2_5_6,
    RingelNine.chirotope_2_5_8,
    RingelNine.chirotope_2_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_11 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 6 *
        RingelNine.magnitude v 2 4 5 <
      RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 2 4 6 := by
  have hgp := rankThreeBracket_plucker (v 2) (v 1) (v 4) (v 5) (v 6)
  have hperm_0 :
      rankThreeBracket (v 2) (v 1) (v 4) =
        -rankThreeBracket (v 1) (v 2) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 2) (v 1) (v 5) =
        -rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 2) (v 1) (v 6) =
        -rankThreeBracket (v 1) (v 2) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_4,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_2_4_5,
    RingelNine.chirotope_2_4_6,
    RingelNine.chirotope_2_5_6,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_12 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 7 *
        RingelNine.magnitude v 1 2 6 <
      RingelNine.magnitude v 0 1 2 *
        RingelNine.magnitude v 1 6 7 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 0) (v 2) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 1) (v 0) (v 2) =
        -rankThreeBracket (v 0) (v 1) (v 2) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 1) (v 0) (v 6) =
        -rankThreeBracket (v 0) (v 1) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 1) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 1) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_2,
    RingelNine.chirotope_0_1_6,
    RingelNine.chirotope_0_1_7,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_13 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 7 *
        RingelNine.magnitude v 1 2 4 <
      RingelNine.magnitude v 0 1 2 *
        RingelNine.magnitude v 1 4 7 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 0) (v 2) (v 4) (v 7)
  have hperm_0 :
      rankThreeBracket (v 1) (v 0) (v 2) =
        -rankThreeBracket (v 0) (v 1) (v 2) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 1) (v 0) (v 4) =
        -rankThreeBracket (v 0) (v 1) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 1) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 1) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_2,
    RingelNine.chirotope_0_1_4,
    RingelNine.chirotope_0_1_7,
    RingelNine.chirotope_1_2_4,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_4_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_14 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 5 *
        RingelNine.magnitude v 1 6 8 <
      RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 1 5 6 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 0) (v 5) (v 6) (v 8)
  have hperm_0 :
      rankThreeBracket (v 1) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 1) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 1) (v 0) (v 6) =
        -rankThreeBracket (v 0) (v 1) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 1) (v 0) (v 8) =
        -rankThreeBracket (v 0) (v 1) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_5,
    RingelNine.chirotope_0_1_6,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_1_5_6,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_1_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_15 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 3 *
        RingelNine.magnitude v 1 4 7 <
      RingelNine.magnitude v 0 1 4 *
        RingelNine.magnitude v 1 3 7 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 0) (v 3) (v 4) (v 7)
  have hperm_0 :
      rankThreeBracket (v 1) (v 0) (v 3) =
        -rankThreeBracket (v 0) (v 1) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 1) (v 0) (v 4) =
        -rankThreeBracket (v 0) (v 1) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 1) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 1) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_3,
    RingelNine.chirotope_0_1_4,
    RingelNine.chirotope_0_1_7,
    RingelNine.chirotope_1_3_4,
    RingelNine.chirotope_1_3_7,
    RingelNine.chirotope_1_4_7,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_16 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 8 *
        RingelNine.magnitude v 1 3 7 <
      RingelNine.magnitude v 1 2 3 *
        RingelNine.magnitude v 1 7 8 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 2) (v 3) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 3 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_1_3_7,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_1_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_17 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 8 *
        RingelNine.magnitude v 1 3 7 <
      RingelNine.magnitude v 1 2 3 *
        RingelNine.magnitude v 1 7 8 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 2) (v 3) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 3 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_1_3_7,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_1_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_18 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 1 7 8 <
      RingelNine.magnitude v 1 2 8 *
        RingelNine.magnitude v 1 5 7 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 2) (v 5) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_1_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_19 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 1 7 8 <
      RingelNine.magnitude v 1 2 8 *
        RingelNine.magnitude v 1 5 7 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 2) (v 5) (v 7) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_2_8,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_1_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_20 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 3 *
        RingelNine.magnitude v 1 4 6 <
      RingelNine.magnitude v 1 2 4 *
        RingelNine.magnitude v 1 3 6 := by
  have hgp := rankThreeBracket_plucker (v 1) (v 2) (v 3) (v 4) (v 6)
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_2_4,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_1_3_4,
    RingelNine.chirotope_1_3_6,
    RingelNine.chirotope_1_4_6,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_21 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 2 7 8 <
      RingelNine.magnitude v 0 2 8 *
        RingelNine.magnitude v 5 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 2) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 5) (v 7) =
        rankThreeBracket (v 5) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 2) (v 7) =
        rankThreeBracket (v 2) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 2) (v 5) =
        rankThreeBracket (v 2) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_8,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_2_5_8,
    RingelNine.chirotope_2_7_8,
    RingelNine.chirotope_5_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_22 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 1 6 8 <
      RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 5 6 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 1) (v 5) (v 6)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 5) (v 6) =
        rankThreeBracket (v 5) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 1) (v 6) =
        rankThreeBracket (v 1) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_1_6_8,
    RingelNine.chirotope_5_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_23 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 1 4 8 <
      RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 4 5 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 1) (v 4) (v 5)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 4) =
        rankThreeBracket (v 0) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 1) (v 4) =
        rankThreeBracket (v 1) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_4_8,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_1_4_8,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_4_5_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_24 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 1 8 *
        RingelNine.magnitude v 5 7 8 <
      RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 1 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 1) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 5) (v 7) =
        rankThreeBracket (v 5) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 1) (v 7) =
        rankThreeBracket (v 1) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_8,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_1_7_8,
    RingelNine.chirotope_5_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_25 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 4 8 *
        RingelNine.magnitude v 6 7 8 <
      RingelNine.magnitude v 0 6 8 *
        RingelNine.magnitude v 4 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 4) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 4) =
        rankThreeBracket (v 0) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 4) (v 7) =
        rankThreeBracket (v 4) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 4) (v 6) =
        rankThreeBracket (v 4) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_4_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_4_6_8,
    RingelNine.chirotope_4_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_26 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 4 8 *
        RingelNine.magnitude v 6 7 8 <
      RingelNine.magnitude v 0 6 8 *
        RingelNine.magnitude v 4 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 4) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 4) =
        rankThreeBracket (v 0) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 4) (v 7) =
        rankThreeBracket (v 4) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 4) (v 6) =
        rankThreeBracket (v 4) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_4_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_4_6_8,
    RingelNine.chirotope_4_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_27 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 6 8 *
        RingelNine.magnitude v 3 7 8 <
      RingelNine.magnitude v 0 3 8 *
        RingelNine.magnitude v 6 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 3) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 3) =
        rankThreeBracket (v 0) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 3) (v 7) =
        rankThreeBracket (v 3) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 3) (v 6) =
        rankThreeBracket (v 3) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_3_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_3_6_8,
    RingelNine.chirotope_3_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_28 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 6 8 *
        RingelNine.magnitude v 5 7 8 <
      RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 6 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 5) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 5) (v 7) =
        rankThreeBracket (v 5) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 5) (v 6) =
        rankThreeBracket (v 5) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 5 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_5_6_8,
    RingelNine.chirotope_5_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_29 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 6 8 *
        RingelNine.magnitude v 5 7 8 <
      RingelNine.magnitude v 0 5 8 *
        RingelNine.magnitude v 6 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 0) (v 5) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 0) (v 6) =
        rankThreeBracket (v 0) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 5) (v 7) =
        rankThreeBracket (v 5) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 0) (v 7) =
        rankThreeBracket (v 0) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 5) (v 6) =
        rankThreeBracket (v 5) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 5 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_5_8,
    RingelNine.chirotope_0_6_8,
    RingelNine.chirotope_0_7_8,
    RingelNine.chirotope_5_6_8,
    RingelNine.chirotope_5_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_30 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 2 3 8 *
        RingelNine.magnitude v 6 7 8 <
      RingelNine.magnitude v 2 6 8 *
        RingelNine.magnitude v 3 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 2) (v 3) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 2) (v 6) =
        rankThreeBracket (v 2) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 3) (v 7) =
        rankThreeBracket (v 3) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 2) (v 7) =
        rankThreeBracket (v 2) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 3) (v 6) =
        rankThreeBracket (v 3) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 2 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_2_3_8,
    RingelNine.chirotope_2_6_8,
    RingelNine.chirotope_2_7_8,
    RingelNine.chirotope_3_6_8,
    RingelNine.chirotope_3_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_31 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 2 3 8 *
        RingelNine.magnitude v 6 7 8 <
      RingelNine.magnitude v 2 6 8 *
        RingelNine.magnitude v 3 7 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 2) (v 3) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 8) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 6) (v 7) =
        rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 2) (v 6) =
        rankThreeBracket (v 2) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 3) (v 7) =
        rankThreeBracket (v 3) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 2) (v 7) =
        rankThreeBracket (v 2) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 3) (v 6) =
        rankThreeBracket (v 3) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 2 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_2_3_8,
    RingelNine.chirotope_2_6_8,
    RingelNine.chirotope_2_7_8,
    RingelNine.chirotope_3_6_8,
    RingelNine.chirotope_3_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_32 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 3 8 *
        RingelNine.magnitude v 4 6 8 <
      RingelNine.magnitude v 1 6 8 *
        RingelNine.magnitude v 3 4 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 1) (v 3) (v 4) (v 6)
  have hperm_0 :
      rankThreeBracket (v 8) (v 1) (v 3) =
        rankThreeBracket (v 1) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 4) (v 6) =
        rankThreeBracket (v 4) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 1) (v 4) =
        rankThreeBracket (v 1) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 3) (v 6) =
        rankThreeBracket (v 3) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 1) (v 6) =
        rankThreeBracket (v 1) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 4 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_1_4_8,
    RingelNine.chirotope_1_6_8,
    RingelNine.chirotope_3_4_8,
    RingelNine.chirotope_3_6_8,
    RingelNine.chirotope_4_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_33 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 3 8 *
        RingelNine.magnitude v 4 5 8 <
      RingelNine.magnitude v 1 4 8 *
        RingelNine.magnitude v 3 5 8 := by
  have hgp := rankThreeBracket_plucker (v 8) (v 1) (v 3) (v 4) (v 5)
  have hperm_0 :
      rankThreeBracket (v 8) (v 1) (v 3) =
        rankThreeBracket (v 1) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 8) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 8) (v 1) (v 4) =
        rankThreeBracket (v 1) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 8) (v 3) (v 5) =
        rankThreeBracket (v 3) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 8) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 8) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 4 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_1_4_8,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_3_4_8,
    RingelNine.chirotope_3_5_8,
    RingelNine.chirotope_4_5_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_34 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 4 6 *
        RingelNine.magnitude v 5 6 7 <
      RingelNine.magnitude v 0 6 7 *
        RingelNine.magnitude v 4 5 6 := by
  have hgp := rankThreeBracket_plucker (v 6) (v 0) (v 4) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 6) (v 0) (v 4) =
        rankThreeBracket (v 0) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 6) (v 5) (v 7) =
        -rankThreeBracket (v 5) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 6) (v 0) (v 5) =
        rankThreeBracket (v 0) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 6) (v 4) (v 7) =
        -rankThreeBracket (v 4) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 6) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 6) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_4_6,
    RingelNine.chirotope_0_5_6,
    RingelNine.chirotope_0_6_7,
    RingelNine.chirotope_4_5_6,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_5_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_35 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 3 6 *
        RingelNine.magnitude v 2 6 8 <
      RingelNine.magnitude v 1 6 8 *
        RingelNine.magnitude v 2 3 6 := by
  have hgp := rankThreeBracket_plucker (v 6) (v 1) (v 2) (v 3) (v 8)
  have hperm_0 :
      rankThreeBracket (v 6) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 6) (v 3) (v 8) =
        -rankThreeBracket (v 3) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 6) (v 1) (v 3) =
        rankThreeBracket (v 1) (v 3) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 6) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 6) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 6) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_6,
    RingelNine.chirotope_1_3_6,
    RingelNine.chirotope_1_6_8,
    RingelNine.chirotope_2_3_6,
    RingelNine.chirotope_2_6_8,
    RingelNine.chirotope_3_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_36 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 2 4 6 *
        RingelNine.magnitude v 5 6 8 <
      RingelNine.magnitude v 2 6 8 *
        RingelNine.magnitude v 4 5 6 := by
  have hgp := rankThreeBracket_plucker (v 6) (v 2) (v 4) (v 5) (v 8)
  have hperm_0 :
      rankThreeBracket (v 6) (v 2) (v 4) =
        rankThreeBracket (v 2) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 6) (v 5) (v 8) =
        -rankThreeBracket (v 5) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 6) (v 2) (v 5) =
        rankThreeBracket (v 2) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 6) (v 4) (v 8) =
        -rankThreeBracket (v 4) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 6) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 6) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 6) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_2_4_6,
    RingelNine.chirotope_2_5_6,
    RingelNine.chirotope_2_6_8,
    RingelNine.chirotope_4_5_6,
    RingelNine.chirotope_4_6_8,
    RingelNine.chirotope_5_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_37 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 3 6 7 *
        RingelNine.magnitude v 4 5 6 <
      RingelNine.magnitude v 3 4 6 *
        RingelNine.magnitude v 5 6 7 := by
  have hgp := rankThreeBracket_plucker (v 6) (v 3) (v 4) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 6) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 6) (v 5) (v 7) =
        -rankThreeBracket (v 5) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 6) (v 3) (v 5) =
        rankThreeBracket (v 3) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 6) (v 4) (v 7) =
        -rankThreeBracket (v 4) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 6) (v 3) (v 7) =
        -rankThreeBracket (v 3) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 6) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 3 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_3_4_6,
    RingelNine.chirotope_3_5_6,
    RingelNine.chirotope_3_6_7,
    RingelNine.chirotope_4_5_6,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_5_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_38 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 3 6 7 *
        RingelNine.magnitude v 4 5 6 <
      RingelNine.magnitude v 3 4 6 *
        RingelNine.magnitude v 5 6 7 := by
  have hgp := rankThreeBracket_plucker (v 6) (v 3) (v 4) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 6) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 6) (v 5) (v 7) =
        -rankThreeBracket (v 5) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 6) (v 3) (v 5) =
        rankThreeBracket (v 3) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 6) (v 4) (v 7) =
        -rankThreeBracket (v 4) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 6) (v 3) (v 7) =
        -rankThreeBracket (v 3) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 6) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 3 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_3_4_6,
    RingelNine.chirotope_3_5_6,
    RingelNine.chirotope_3_6_7,
    RingelNine.chirotope_4_5_6,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_5_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_39 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 4 *
        RingelNine.magnitude v 3 4 5 <
      RingelNine.magnitude v 0 3 4 *
        RingelNine.magnitude v 2 4 5 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 0) (v 2) (v 3) (v 5)
  have hperm_0 :
      rankThreeBracket (v 4) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 4) (v 3) (v 5) =
        -rankThreeBracket (v 3) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 0) (v 3) =
        rankThreeBracket (v 0) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 4) (v 2) (v 5) =
        -rankThreeBracket (v 2) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 4) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_4,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_2_3_4,
    RingelNine.chirotope_2_4_5,
    RingelNine.chirotope_3_4_5,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_40 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 4 *
        RingelNine.magnitude v 3 4 5 <
      RingelNine.magnitude v 0 3 4 *
        RingelNine.magnitude v 2 4 5 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 0) (v 2) (v 3) (v 5)
  have hperm_0 :
      rankThreeBracket (v 4) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 4) (v 3) (v 5) =
        -rankThreeBracket (v 3) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 0) (v 3) =
        rankThreeBracket (v 0) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 4) (v 2) (v 5) =
        -rankThreeBracket (v 2) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 4) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_4,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_2_3_4,
    RingelNine.chirotope_2_4_5,
    RingelNine.chirotope_3_4_5,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_41 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 3 4 *
        RingelNine.magnitude v 4 5 7 <
      RingelNine.magnitude v 0 4 7 *
        RingelNine.magnitude v 3 4 5 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 0) (v 3) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 4) (v 0) (v 3) =
        rankThreeBracket (v 0) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 4) (v 3) (v 7) =
        -rankThreeBracket (v 3) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 4) (v 3) (v 5) =
        -rankThreeBracket (v 3) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 4 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_0_4_7,
    RingelNine.chirotope_3_4_5,
    RingelNine.chirotope_3_4_7,
    RingelNine.chirotope_4_5_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_42 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 3 4 *
        RingelNine.magnitude v 4 5 7 <
      RingelNine.magnitude v 0 4 7 *
        RingelNine.magnitude v 3 4 5 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 0) (v 3) (v 5) (v 7)
  have hperm_0 :
      rankThreeBracket (v 4) (v 0) (v 3) =
        rankThreeBracket (v 0) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 0) (v 5) =
        -rankThreeBracket (v 0) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 4) (v 3) (v 7) =
        -rankThreeBracket (v 3) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 4) (v 3) (v 5) =
        -rankThreeBracket (v 3) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 4 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_4_5,
    RingelNine.chirotope_0_4_7,
    RingelNine.chirotope_3_4_5,
    RingelNine.chirotope_3_4_7,
    RingelNine.chirotope_4_5_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_43 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 4 7 *
        RingelNine.magnitude v 4 5 6 <
      RingelNine.magnitude v 1 4 6 *
        RingelNine.magnitude v 4 5 7 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 1) (v 5) (v 6) (v 7)
  have hperm_0 :
      rankThreeBracket (v 4) (v 1) (v 5) =
        -rankThreeBracket (v 1) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 1) (v 6) =
        -rankThreeBracket (v 1) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 1) (v 7) =
        -rankThreeBracket (v 1) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_4_5,
    RingelNine.chirotope_1_4_6,
    RingelNine.chirotope_1_4_7,
    RingelNine.chirotope_4_5_6,
    RingelNine.chirotope_4_5_7,
    RingelNine.chirotope_4_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_44 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 3 4 6 *
        RingelNine.magnitude v 4 7 8 <
      RingelNine.magnitude v 3 4 7 *
        RingelNine.magnitude v 4 6 8 := by
  have hgp := rankThreeBracket_plucker (v 4) (v 3) (v 6) (v 7) (v 8)
  have hperm_0 :
      rankThreeBracket (v 4) (v 3) (v 6) =
        -rankThreeBracket (v 3) (v 4) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 4) (v 3) (v 7) =
        -rankThreeBracket (v 3) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 4) (v 3) (v 8) =
        -rankThreeBracket (v 3) (v 4) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 3 4 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_3_4_6,
    RingelNine.chirotope_3_4_7,
    RingelNine.chirotope_3_4_8,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_4_6_8,
    RingelNine.chirotope_4_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_45 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 3 8 *
        RingelNine.magnitude v 1 2 3 <
      RingelNine.magnitude v 0 1 3 *
        RingelNine.magnitude v 2 3 8 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 0) (v 1) (v 2) (v 8)
  have hperm_0 :
      rankThreeBracket (v 3) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 3) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 3) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 3) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 3) (v 0) (v 8) =
        -rankThreeBracket (v 0) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 3) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 1 3 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_3,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_3_8,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_2_3_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_46 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 3 8 *
        RingelNine.magnitude v 2 3 4 <
      RingelNine.magnitude v 0 3 4 *
        RingelNine.magnitude v 2 3 8 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 0) (v 2) (v 4) (v 8)
  have hperm_0 :
      rankThreeBracket (v 3) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 3) (v 0) (v 4) =
        -rankThreeBracket (v 0) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 3) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 3) (v 0) (v 8) =
        -rankThreeBracket (v 0) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 3) (v 2) (v 4) =
        -rankThreeBracket (v 2) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 2 3 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 4 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_2_3,
    RingelNine.chirotope_0_3_4,
    RingelNine.chirotope_0_3_8,
    RingelNine.chirotope_2_3_4,
    RingelNine.chirotope_2_3_8,
    RingelNine.chirotope_3_4_8,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_47 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 3 6 *
        RingelNine.magnitude v 3 7 8 <
      RingelNine.magnitude v 0 3 8 *
        RingelNine.magnitude v 3 6 7 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 0) (v 6) (v 7) (v 8)
  have hperm_0 :
      rankThreeBracket (v 3) (v 0) (v 6) =
        -rankThreeBracket (v 0) (v 3) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 3) (v 0) (v 7) =
        -rankThreeBracket (v 0) (v 3) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 3) (v 0) (v 8) =
        -rankThreeBracket (v 0) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_4] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 3 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_3_6,
    RingelNine.chirotope_0_3_7,
    RingelNine.chirotope_0_3_8,
    RingelNine.chirotope_3_6_7,
    RingelNine.chirotope_3_6_8,
    RingelNine.chirotope_3_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_48 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 3 *
        RingelNine.magnitude v 3 4 8 <
      RingelNine.magnitude v 1 3 8 *
        RingelNine.magnitude v 2 3 4 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 1) (v 2) (v 4) (v 8)
  have hperm_0 :
      rankThreeBracket (v 3) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 3) (v 1) (v 4) =
        -rankThreeBracket (v 1) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 3) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 3) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 3) (v 2) (v 4) =
        -rankThreeBracket (v 2) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 3 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_3_4,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_2_3_4,
    RingelNine.chirotope_2_3_8,
    RingelNine.chirotope_3_4_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_49 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 2 3 *
        RingelNine.magnitude v 3 4 8 <
      RingelNine.magnitude v 1 3 8 *
        RingelNine.magnitude v 2 3 4 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 1) (v 2) (v 4) (v 8)
  have hperm_0 :
      rankThreeBracket (v 3) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 3) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 3) (v 1) (v 4) =
        -rankThreeBracket (v 1) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 3) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 3) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 3) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 3) (v 2) (v 4) =
        -rankThreeBracket (v 2) (v 3) (v 4) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 3 4 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 3 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_3,
    RingelNine.chirotope_1_3_4,
    RingelNine.chirotope_1_3_8,
    RingelNine.chirotope_2_3_4,
    RingelNine.chirotope_2_3_8,
    RingelNine.chirotope_3_4_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_50 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 3 4 6 *
        RingelNine.magnitude v 3 5 8 <
      RingelNine.magnitude v 3 4 8 *
        RingelNine.magnitude v 3 5 6 := by
  have hgp := rankThreeBracket_plucker (v 3) (v 4) (v 5) (v 6) (v 8)
  have hpositive_1 : 0 < RingelNine.magnitude v 3 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 6 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_3_4_5,
    RingelNine.chirotope_3_4_6,
    RingelNine.chirotope_3_4_8,
    RingelNine.chirotope_3_5_6,
    RingelNine.chirotope_3_5_8,
    RingelNine.chirotope_3_6_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_51 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 0 2 5 *
        RingelNine.magnitude v 1 5 6 <
      RingelNine.magnitude v 0 5 6 *
        RingelNine.magnitude v 1 2 5 := by
  have hgp := rankThreeBracket_plucker (v 5) (v 0) (v 1) (v 2) (v 6)
  have hperm_0 :
      rankThreeBracket (v 5) (v 0) (v 1) =
        rankThreeBracket (v 0) (v 1) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 5) (v 2) (v 6) =
        -rankThreeBracket (v 2) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 5) (v 0) (v 2) =
        rankThreeBracket (v 0) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 5) (v 1) (v 6) =
        -rankThreeBracket (v 1) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 5) (v 0) (v 6) =
        -rankThreeBracket (v 0) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 5) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 0 1 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_0_1_5,
    RingelNine.chirotope_0_2_5,
    RingelNine.chirotope_0_5_6,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_5_6,
    RingelNine.chirotope_2_5_6,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_52 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 5 7 *
        RingelNine.magnitude v 2 5 8 <
      RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 5 7 8 := by
  have hgp := rankThreeBracket_plucker (v 5) (v 1) (v 2) (v 7) (v 8)
  have hperm_0 :
      rankThreeBracket (v 5) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 5) (v 1) (v 7) =
        -rankThreeBracket (v 1) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 5) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 5) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 5) (v 2) (v 7) =
        -rankThreeBracket (v 2) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_2_5_7,
    RingelNine.chirotope_2_5_8,
    RingelNine.chirotope_5_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_53 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 5 7 *
        RingelNine.magnitude v 2 5 8 <
      RingelNine.magnitude v 1 2 5 *
        RingelNine.magnitude v 5 7 8 := by
  have hgp := rankThreeBracket_plucker (v 5) (v 1) (v 2) (v 7) (v 8)
  have hperm_0 :
      rankThreeBracket (v 5) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 5) (v 1) (v 7) =
        -rankThreeBracket (v 1) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 5) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 5) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 5) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 5) (v 2) (v 7) =
        -rankThreeBracket (v 2) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 5 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 2 5 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_5,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_1_5_8,
    RingelNine.chirotope_2_5_7,
    RingelNine.chirotope_2_5_8,
    RingelNine.chirotope_5_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_54 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 2 4 5 *
        RingelNine.magnitude v 3 5 6 <
      RingelNine.magnitude v 2 3 5 *
        RingelNine.magnitude v 4 5 6 := by
  have hgp := rankThreeBracket_plucker (v 5) (v 2) (v 3) (v 4) (v 6)
  have hperm_0 :
      rankThreeBracket (v 5) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 5) (v 4) (v 6) =
        -rankThreeBracket (v 4) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 5) (v 2) (v 4) =
        rankThreeBracket (v 2) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 5) (v 3) (v 6) =
        -rankThreeBracket (v 3) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 5) (v 2) (v 6) =
        -rankThreeBracket (v 2) (v 5) (v 6) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 5) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 5) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 2 5 6 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 4 5 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_2_3_5,
    RingelNine.chirotope_2_4_5,
    RingelNine.chirotope_2_5_6,
    RingelNine.chirotope_3_4_5,
    RingelNine.chirotope_3_5_6,
    RingelNine.chirotope_4_5_6,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_55 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 7 8 *
        RingelNine.magnitude v 2 5 7 <
      RingelNine.magnitude v 1 5 7 *
        RingelNine.magnitude v 2 7 8 := by
  have hgp := rankThreeBracket_plucker (v 7) (v 1) (v 2) (v 5) (v 8)
  have hperm_0 :
      rankThreeBracket (v 7) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 7) (v 5) (v 8) =
        -rankThreeBracket (v 5) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 7) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 7) (v 2) (v 8) =
        -rankThreeBracket (v 2) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 7) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 7) (v 2) (v 5) =
        rankThreeBracket (v 2) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 5 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_1_7_8,
    RingelNine.chirotope_2_5_7,
    RingelNine.chirotope_2_7_8,
    RingelNine.chirotope_5_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_56 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 5 7 *
        RingelNine.magnitude v 2 3 7 <
      RingelNine.magnitude v 1 3 7 *
        RingelNine.magnitude v 2 5 7 := by
  have hgp := rankThreeBracket_plucker (v 7) (v 1) (v 2) (v 3) (v 5)
  have hperm_0 :
      rankThreeBracket (v 7) (v 1) (v 2) =
        rankThreeBracket (v 1) (v 2) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 7) (v 3) (v 5) =
        rankThreeBracket (v 3) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 7) (v 1) (v 3) =
        rankThreeBracket (v 1) (v 3) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 7) (v 2) (v 5) =
        rankThreeBracket (v 2) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 7) (v 1) (v 5) =
        rankThreeBracket (v 1) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 7) (v 2) (v 3) =
        rankThreeBracket (v 2) (v 3) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 2 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 3 5 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_2_7,
    RingelNine.chirotope_1_3_7,
    RingelNine.chirotope_1_5_7,
    RingelNine.chirotope_2_3_7,
    RingelNine.chirotope_2_5_7,
    RingelNine.chirotope_3_5_7,
    one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_57 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 1 6 7 *
        RingelNine.magnitude v 4 7 8 <
      RingelNine.magnitude v 1 4 7 *
        RingelNine.magnitude v 6 7 8 := by
  have hgp := rankThreeBracket_plucker (v 7) (v 1) (v 4) (v 6) (v 8)
  have hperm_0 :
      rankThreeBracket (v 7) (v 1) (v 4) =
        rankThreeBracket (v 1) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 7) (v 6) (v 8) =
        -rankThreeBracket (v 6) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 7) (v 1) (v 6) =
        rankThreeBracket (v 1) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 7) (v 4) (v 8) =
        -rankThreeBracket (v 4) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 7) (v 1) (v 8) =
        -rankThreeBracket (v 1) (v 7) (v 8) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 7) (v 4) (v 6) =
        rankThreeBracket (v 4) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 1 7 8 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_1_4_7,
    RingelNine.chirotope_1_6_7,
    RingelNine.chirotope_1_7_8,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_4_7_8,
    RingelNine.chirotope_6_7_8,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

private theorem row_58 (v : Fin 9 → RankThreeVector)
    (hv : RankThreeVectorRealizes ringelNineChirotope v) :
    RingelNine.magnitude v 3 4 7 *
        RingelNine.magnitude v 5 6 7 <
      RingelNine.magnitude v 3 6 7 *
        RingelNine.magnitude v 4 5 7 := by
  have hgp := rankThreeBracket_plucker (v 7) (v 3) (v 4) (v 5) (v 6)
  have hperm_0 :
      rankThreeBracket (v 7) (v 3) (v 4) =
        rankThreeBracket (v 3) (v 4) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_1 :
      rankThreeBracket (v 7) (v 5) (v 6) =
        rankThreeBracket (v 5) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_2 :
      rankThreeBracket (v 7) (v 3) (v 5) =
        rankThreeBracket (v 3) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_3 :
      rankThreeBracket (v 7) (v 4) (v 6) =
        rankThreeBracket (v 4) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_4 :
      rankThreeBracket (v 7) (v 3) (v 6) =
        rankThreeBracket (v 3) (v 6) (v 7) := by
    simp only [rankThreeBracket]
    ring
  have hperm_5 :
      rankThreeBracket (v 7) (v 4) (v 5) =
        rankThreeBracket (v 4) (v 5) (v 7) := by
    simp only [rankThreeBracket]
    ring
  rw [hperm_0, hperm_1, hperm_2, hperm_3, hperm_4, hperm_5] at hgp
  have hpositive_1 : 0 < RingelNine.magnitude v 3 5 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  have hpositive_2 : 0 < RingelNine.magnitude v 4 6 7 := by
    exact hv.normalizedBracket_pos (by decide) (by decide) (by decide)
  simp only [RingelNine.magnitude, normalizedRankThreeBracket,
    RingelNine.chirotope_3_4_7,
    RingelNine.chirotope_3_5_7,
    RingelNine.chirotope_3_6_7,
    RingelNine.chirotope_4_5_7,
    RingelNine.chirotope_4_6_7,
    RingelNine.chirotope_5_6_7,
    one_mul, neg_one_mul] at hpositive_1 hpositive_2 ⊢
  nlinarith [mul_pos hpositive_1 hpositive_2]

/-- The exact 59-row final-polynomial certificate excludes homogeneous
realizations of the frozen Ringel sign pattern. -/
theorem ringelNine_not_rankThreeVectorRealizable :
    ¬RankThreeVectorRealizable ringelNineChirotope := by
  rintro ⟨v, hv⟩
  let lhs_00 : ℝ :=
    RingelNine.magnitude v 0 2 8 *
      RingelNine.magnitude v 0 6 7
  let rhs_00 : ℝ :=
    RingelNine.magnitude v 0 2 7 *
      RingelNine.magnitude v 0 6 8
  have hrow_00 : lhs_00 < rhs_00 := by
    exact row_00 v hv
  have hlhs_00 : 0 < lhs_00 := by
    dsimp only [lhs_00]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_00 : 0 < rhs_00 := by
    dsimp only [rhs_00]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_01 : ℝ :=
    RingelNine.magnitude v 0 2 6 *
      RingelNine.magnitude v 0 3 4
  let rhs_01 : ℝ :=
    RingelNine.magnitude v 0 2 4 *
      RingelNine.magnitude v 0 3 6
  have hrow_01 : lhs_01 < rhs_01 := by
    exact row_01 v hv
  have hlhs_01 : 0 < lhs_01 := by
    dsimp only [lhs_01]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_01 : 0 < rhs_01 := by
    dsimp only [rhs_01]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_02 : ℝ :=
    RingelNine.magnitude v 0 1 4 *
      RingelNine.magnitude v 0 5 8
  let rhs_02 : ℝ :=
    RingelNine.magnitude v 0 1 5 *
      RingelNine.magnitude v 0 4 8
  have hrow_02 : lhs_02 < rhs_02 := by
    exact row_02 v hv
  have hlhs_02 : 0 < lhs_02 := by
    dsimp only [lhs_02]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_02 : 0 < rhs_02 := by
    dsimp only [rhs_02]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_03 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 0 4 7
  let rhs_03 : ℝ :=
    RingelNine.magnitude v 0 1 7 *
      RingelNine.magnitude v 0 4 8
  have hrow_03 : lhs_03 < rhs_03 := by
    exact row_03 v hv
  have hlhs_03 : 0 < lhs_03 := by
    dsimp only [lhs_03]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_03 : 0 < rhs_03 := by
    dsimp only [rhs_03]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_04 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 0 5 7
  let rhs_04 : ℝ :=
    RingelNine.magnitude v 0 1 7 *
      RingelNine.magnitude v 0 5 8
  have hrow_04 : lhs_04 < rhs_04 := by
    exact row_04 v hv
  have hlhs_04 : 0 < lhs_04 := by
    dsimp only [lhs_04]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_04 : 0 < rhs_04 := by
    dsimp only [rhs_04]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_05 : ℝ :=
    RingelNine.magnitude v 0 4 7 *
      RingelNine.magnitude v 0 5 6
  let rhs_05 : ℝ :=
    RingelNine.magnitude v 0 4 6 *
      RingelNine.magnitude v 0 5 7
  have hrow_05 : lhs_05 < rhs_05 := by
    exact row_05 v hv
  have hlhs_05 : 0 < lhs_05 := by
    dsimp only [lhs_05]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_05 : 0 < rhs_05 := by
    dsimp only [rhs_05]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_06 : ℝ :=
    RingelNine.magnitude v 0 1 2 *
      RingelNine.magnitude v 2 3 4
  let rhs_06 : ℝ :=
    RingelNine.magnitude v 0 2 4 *
      RingelNine.magnitude v 1 2 3
  have hrow_06 : lhs_06 < rhs_06 := by
    exact row_06 v hv
  have hlhs_06 : 0 < lhs_06 := by
    dsimp only [lhs_06]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_06 : 0 < rhs_06 := by
    dsimp only [rhs_06]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_07 : ℝ :=
    RingelNine.magnitude v 0 1 2 *
      RingelNine.magnitude v 2 3 5
  let rhs_07 : ℝ :=
    RingelNine.magnitude v 0 2 5 *
      RingelNine.magnitude v 1 2 3
  have hrow_07 : lhs_07 < rhs_07 := by
    exact row_07 v hv
  have hlhs_07 : 0 < lhs_07 := by
    dsimp only [lhs_07]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_07 : 0 < rhs_07 := by
    dsimp only [rhs_07]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_08 : ℝ :=
    RingelNine.magnitude v 0 2 7 *
      RingelNine.magnitude v 2 3 6
  let rhs_08 : ℝ :=
    RingelNine.magnitude v 0 2 6 *
      RingelNine.magnitude v 2 3 7
  have hrow_08 : lhs_08 < rhs_08 := by
    exact row_08 v hv
  have hlhs_08 : 0 < lhs_08 := by
    dsimp only [lhs_08]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_08 : 0 < rhs_08 := by
    dsimp only [rhs_08]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_09 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 2 6 8
  let rhs_09 : ℝ :=
    RingelNine.magnitude v 1 2 6 *
      RingelNine.magnitude v 2 5 8
  have hrow_09 : lhs_09 < rhs_09 := by
    exact row_09 v hv
  have hlhs_09 : 0 < lhs_09 := by
    dsimp only [lhs_09]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_09 : 0 < rhs_09 := by
    dsimp only [rhs_09]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_10 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 2 6 8
  let rhs_10 : ℝ :=
    RingelNine.magnitude v 1 2 6 *
      RingelNine.magnitude v 2 5 8
  have hrow_10 : lhs_10 < rhs_10 := by
    exact row_10 v hv
  have hlhs_10 : 0 < lhs_10 := by
    dsimp only [lhs_10]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_10 : 0 < rhs_10 := by
    dsimp only [rhs_10]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_11 : ℝ :=
    RingelNine.magnitude v 1 2 6 *
      RingelNine.magnitude v 2 4 5
  let rhs_11 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 2 4 6
  have hrow_11 : lhs_11 < rhs_11 := by
    exact row_11 v hv
  have hlhs_11 : 0 < lhs_11 := by
    dsimp only [lhs_11]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_11 : 0 < rhs_11 := by
    dsimp only [rhs_11]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_12 : ℝ :=
    RingelNine.magnitude v 0 1 7 *
      RingelNine.magnitude v 1 2 6
  let rhs_12 : ℝ :=
    RingelNine.magnitude v 0 1 2 *
      RingelNine.magnitude v 1 6 7
  have hrow_12 : lhs_12 < rhs_12 := by
    exact row_12 v hv
  have hlhs_12 : 0 < lhs_12 := by
    dsimp only [lhs_12]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_12 : 0 < rhs_12 := by
    dsimp only [rhs_12]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_13 : ℝ :=
    RingelNine.magnitude v 0 1 7 *
      RingelNine.magnitude v 1 2 4
  let rhs_13 : ℝ :=
    RingelNine.magnitude v 0 1 2 *
      RingelNine.magnitude v 1 4 7
  have hrow_13 : lhs_13 < rhs_13 := by
    exact row_13 v hv
  have hlhs_13 : 0 < lhs_13 := by
    dsimp only [lhs_13]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_13 : 0 < rhs_13 := by
    dsimp only [rhs_13]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_14 : ℝ :=
    RingelNine.magnitude v 0 1 5 *
      RingelNine.magnitude v 1 6 8
  let rhs_14 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 1 5 6
  have hrow_14 : lhs_14 < rhs_14 := by
    exact row_14 v hv
  have hlhs_14 : 0 < lhs_14 := by
    dsimp only [lhs_14]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_14 : 0 < rhs_14 := by
    dsimp only [rhs_14]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_15 : ℝ :=
    RingelNine.magnitude v 0 1 3 *
      RingelNine.magnitude v 1 4 7
  let rhs_15 : ℝ :=
    RingelNine.magnitude v 0 1 4 *
      RingelNine.magnitude v 1 3 7
  have hrow_15 : lhs_15 < rhs_15 := by
    exact row_15 v hv
  have hlhs_15 : 0 < lhs_15 := by
    dsimp only [lhs_15]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_15 : 0 < rhs_15 := by
    dsimp only [rhs_15]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_16 : ℝ :=
    RingelNine.magnitude v 1 2 8 *
      RingelNine.magnitude v 1 3 7
  let rhs_16 : ℝ :=
    RingelNine.magnitude v 1 2 3 *
      RingelNine.magnitude v 1 7 8
  have hrow_16 : lhs_16 < rhs_16 := by
    exact row_16 v hv
  have hlhs_16 : 0 < lhs_16 := by
    dsimp only [lhs_16]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_16 : 0 < rhs_16 := by
    dsimp only [rhs_16]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_17 : ℝ :=
    RingelNine.magnitude v 1 2 8 *
      RingelNine.magnitude v 1 3 7
  let rhs_17 : ℝ :=
    RingelNine.magnitude v 1 2 3 *
      RingelNine.magnitude v 1 7 8
  have hrow_17 : lhs_17 < rhs_17 := by
    exact row_17 v hv
  have hlhs_17 : 0 < lhs_17 := by
    dsimp only [lhs_17]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_17 : 0 < rhs_17 := by
    dsimp only [rhs_17]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_18 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 1 7 8
  let rhs_18 : ℝ :=
    RingelNine.magnitude v 1 2 8 *
      RingelNine.magnitude v 1 5 7
  have hrow_18 : lhs_18 < rhs_18 := by
    exact row_18 v hv
  have hlhs_18 : 0 < lhs_18 := by
    dsimp only [lhs_18]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_18 : 0 < rhs_18 := by
    dsimp only [rhs_18]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_19 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 1 7 8
  let rhs_19 : ℝ :=
    RingelNine.magnitude v 1 2 8 *
      RingelNine.magnitude v 1 5 7
  have hrow_19 : lhs_19 < rhs_19 := by
    exact row_19 v hv
  have hlhs_19 : 0 < lhs_19 := by
    dsimp only [lhs_19]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_19 : 0 < rhs_19 := by
    dsimp only [rhs_19]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_20 : ℝ :=
    RingelNine.magnitude v 1 2 3 *
      RingelNine.magnitude v 1 4 6
  let rhs_20 : ℝ :=
    RingelNine.magnitude v 1 2 4 *
      RingelNine.magnitude v 1 3 6
  have hrow_20 : lhs_20 < rhs_20 := by
    exact row_20 v hv
  have hlhs_20 : 0 < lhs_20 := by
    dsimp only [lhs_20]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_20 : 0 < rhs_20 := by
    dsimp only [rhs_20]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_21 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 2 7 8
  let rhs_21 : ℝ :=
    RingelNine.magnitude v 0 2 8 *
      RingelNine.magnitude v 5 7 8
  have hrow_21 : lhs_21 < rhs_21 := by
    exact row_21 v hv
  have hlhs_21 : 0 < lhs_21 := by
    dsimp only [lhs_21]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_21 : 0 < rhs_21 := by
    dsimp only [rhs_21]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_22 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 1 6 8
  let rhs_22 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 5 6 8
  have hrow_22 : lhs_22 < rhs_22 := by
    exact row_22 v hv
  have hlhs_22 : 0 < lhs_22 := by
    dsimp only [lhs_22]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_22 : 0 < rhs_22 := by
    dsimp only [rhs_22]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_23 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 1 4 8
  let rhs_23 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 4 5 8
  have hrow_23 : lhs_23 < rhs_23 := by
    exact row_23 v hv
  have hlhs_23 : 0 < lhs_23 := by
    dsimp only [lhs_23]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_23 : 0 < rhs_23 := by
    dsimp only [rhs_23]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_24 : ℝ :=
    RingelNine.magnitude v 0 1 8 *
      RingelNine.magnitude v 5 7 8
  let rhs_24 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 1 7 8
  have hrow_24 : lhs_24 < rhs_24 := by
    exact row_24 v hv
  have hlhs_24 : 0 < lhs_24 := by
    dsimp only [lhs_24]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_24 : 0 < rhs_24 := by
    dsimp only [rhs_24]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_25 : ℝ :=
    RingelNine.magnitude v 0 4 8 *
      RingelNine.magnitude v 6 7 8
  let rhs_25 : ℝ :=
    RingelNine.magnitude v 0 6 8 *
      RingelNine.magnitude v 4 7 8
  have hrow_25 : lhs_25 < rhs_25 := by
    exact row_25 v hv
  have hlhs_25 : 0 < lhs_25 := by
    dsimp only [lhs_25]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_25 : 0 < rhs_25 := by
    dsimp only [rhs_25]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_26 : ℝ :=
    RingelNine.magnitude v 0 4 8 *
      RingelNine.magnitude v 6 7 8
  let rhs_26 : ℝ :=
    RingelNine.magnitude v 0 6 8 *
      RingelNine.magnitude v 4 7 8
  have hrow_26 : lhs_26 < rhs_26 := by
    exact row_26 v hv
  have hlhs_26 : 0 < lhs_26 := by
    dsimp only [lhs_26]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_26 : 0 < rhs_26 := by
    dsimp only [rhs_26]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_27 : ℝ :=
    RingelNine.magnitude v 0 6 8 *
      RingelNine.magnitude v 3 7 8
  let rhs_27 : ℝ :=
    RingelNine.magnitude v 0 3 8 *
      RingelNine.magnitude v 6 7 8
  have hrow_27 : lhs_27 < rhs_27 := by
    exact row_27 v hv
  have hlhs_27 : 0 < lhs_27 := by
    dsimp only [lhs_27]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_27 : 0 < rhs_27 := by
    dsimp only [rhs_27]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_28 : ℝ :=
    RingelNine.magnitude v 0 6 8 *
      RingelNine.magnitude v 5 7 8
  let rhs_28 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 6 7 8
  have hrow_28 : lhs_28 < rhs_28 := by
    exact row_28 v hv
  have hlhs_28 : 0 < lhs_28 := by
    dsimp only [lhs_28]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_28 : 0 < rhs_28 := by
    dsimp only [rhs_28]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_29 : ℝ :=
    RingelNine.magnitude v 0 6 8 *
      RingelNine.magnitude v 5 7 8
  let rhs_29 : ℝ :=
    RingelNine.magnitude v 0 5 8 *
      RingelNine.magnitude v 6 7 8
  have hrow_29 : lhs_29 < rhs_29 := by
    exact row_29 v hv
  have hlhs_29 : 0 < lhs_29 := by
    dsimp only [lhs_29]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_29 : 0 < rhs_29 := by
    dsimp only [rhs_29]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_30 : ℝ :=
    RingelNine.magnitude v 2 3 8 *
      RingelNine.magnitude v 6 7 8
  let rhs_30 : ℝ :=
    RingelNine.magnitude v 2 6 8 *
      RingelNine.magnitude v 3 7 8
  have hrow_30 : lhs_30 < rhs_30 := by
    exact row_30 v hv
  have hlhs_30 : 0 < lhs_30 := by
    dsimp only [lhs_30]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_30 : 0 < rhs_30 := by
    dsimp only [rhs_30]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_31 : ℝ :=
    RingelNine.magnitude v 2 3 8 *
      RingelNine.magnitude v 6 7 8
  let rhs_31 : ℝ :=
    RingelNine.magnitude v 2 6 8 *
      RingelNine.magnitude v 3 7 8
  have hrow_31 : lhs_31 < rhs_31 := by
    exact row_31 v hv
  have hlhs_31 : 0 < lhs_31 := by
    dsimp only [lhs_31]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_31 : 0 < rhs_31 := by
    dsimp only [rhs_31]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_32 : ℝ :=
    RingelNine.magnitude v 1 3 8 *
      RingelNine.magnitude v 4 6 8
  let rhs_32 : ℝ :=
    RingelNine.magnitude v 1 6 8 *
      RingelNine.magnitude v 3 4 8
  have hrow_32 : lhs_32 < rhs_32 := by
    exact row_32 v hv
  have hlhs_32 : 0 < lhs_32 := by
    dsimp only [lhs_32]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_32 : 0 < rhs_32 := by
    dsimp only [rhs_32]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_33 : ℝ :=
    RingelNine.magnitude v 1 3 8 *
      RingelNine.magnitude v 4 5 8
  let rhs_33 : ℝ :=
    RingelNine.magnitude v 1 4 8 *
      RingelNine.magnitude v 3 5 8
  have hrow_33 : lhs_33 < rhs_33 := by
    exact row_33 v hv
  have hlhs_33 : 0 < lhs_33 := by
    dsimp only [lhs_33]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_33 : 0 < rhs_33 := by
    dsimp only [rhs_33]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_34 : ℝ :=
    RingelNine.magnitude v 0 4 6 *
      RingelNine.magnitude v 5 6 7
  let rhs_34 : ℝ :=
    RingelNine.magnitude v 0 6 7 *
      RingelNine.magnitude v 4 5 6
  have hrow_34 : lhs_34 < rhs_34 := by
    exact row_34 v hv
  have hlhs_34 : 0 < lhs_34 := by
    dsimp only [lhs_34]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_34 : 0 < rhs_34 := by
    dsimp only [rhs_34]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_35 : ℝ :=
    RingelNine.magnitude v 1 3 6 *
      RingelNine.magnitude v 2 6 8
  let rhs_35 : ℝ :=
    RingelNine.magnitude v 1 6 8 *
      RingelNine.magnitude v 2 3 6
  have hrow_35 : lhs_35 < rhs_35 := by
    exact row_35 v hv
  have hlhs_35 : 0 < lhs_35 := by
    dsimp only [lhs_35]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_35 : 0 < rhs_35 := by
    dsimp only [rhs_35]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_36 : ℝ :=
    RingelNine.magnitude v 2 4 6 *
      RingelNine.magnitude v 5 6 8
  let rhs_36 : ℝ :=
    RingelNine.magnitude v 2 6 8 *
      RingelNine.magnitude v 4 5 6
  have hrow_36 : lhs_36 < rhs_36 := by
    exact row_36 v hv
  have hlhs_36 : 0 < lhs_36 := by
    dsimp only [lhs_36]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_36 : 0 < rhs_36 := by
    dsimp only [rhs_36]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_37 : ℝ :=
    RingelNine.magnitude v 3 6 7 *
      RingelNine.magnitude v 4 5 6
  let rhs_37 : ℝ :=
    RingelNine.magnitude v 3 4 6 *
      RingelNine.magnitude v 5 6 7
  have hrow_37 : lhs_37 < rhs_37 := by
    exact row_37 v hv
  have hlhs_37 : 0 < lhs_37 := by
    dsimp only [lhs_37]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_37 : 0 < rhs_37 := by
    dsimp only [rhs_37]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_38 : ℝ :=
    RingelNine.magnitude v 3 6 7 *
      RingelNine.magnitude v 4 5 6
  let rhs_38 : ℝ :=
    RingelNine.magnitude v 3 4 6 *
      RingelNine.magnitude v 5 6 7
  have hrow_38 : lhs_38 < rhs_38 := by
    exact row_38 v hv
  have hlhs_38 : 0 < lhs_38 := by
    dsimp only [lhs_38]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_38 : 0 < rhs_38 := by
    dsimp only [rhs_38]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_39 : ℝ :=
    RingelNine.magnitude v 0 2 4 *
      RingelNine.magnitude v 3 4 5
  let rhs_39 : ℝ :=
    RingelNine.magnitude v 0 3 4 *
      RingelNine.magnitude v 2 4 5
  have hrow_39 : lhs_39 < rhs_39 := by
    exact row_39 v hv
  have hlhs_39 : 0 < lhs_39 := by
    dsimp only [lhs_39]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_39 : 0 < rhs_39 := by
    dsimp only [rhs_39]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_40 : ℝ :=
    RingelNine.magnitude v 0 2 4 *
      RingelNine.magnitude v 3 4 5
  let rhs_40 : ℝ :=
    RingelNine.magnitude v 0 3 4 *
      RingelNine.magnitude v 2 4 5
  have hrow_40 : lhs_40 < rhs_40 := by
    exact row_40 v hv
  have hlhs_40 : 0 < lhs_40 := by
    dsimp only [lhs_40]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_40 : 0 < rhs_40 := by
    dsimp only [rhs_40]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_41 : ℝ :=
    RingelNine.magnitude v 0 3 4 *
      RingelNine.magnitude v 4 5 7
  let rhs_41 : ℝ :=
    RingelNine.magnitude v 0 4 7 *
      RingelNine.magnitude v 3 4 5
  have hrow_41 : lhs_41 < rhs_41 := by
    exact row_41 v hv
  have hlhs_41 : 0 < lhs_41 := by
    dsimp only [lhs_41]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_41 : 0 < rhs_41 := by
    dsimp only [rhs_41]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_42 : ℝ :=
    RingelNine.magnitude v 0 3 4 *
      RingelNine.magnitude v 4 5 7
  let rhs_42 : ℝ :=
    RingelNine.magnitude v 0 4 7 *
      RingelNine.magnitude v 3 4 5
  have hrow_42 : lhs_42 < rhs_42 := by
    exact row_42 v hv
  have hlhs_42 : 0 < lhs_42 := by
    dsimp only [lhs_42]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_42 : 0 < rhs_42 := by
    dsimp only [rhs_42]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_43 : ℝ :=
    RingelNine.magnitude v 1 4 7 *
      RingelNine.magnitude v 4 5 6
  let rhs_43 : ℝ :=
    RingelNine.magnitude v 1 4 6 *
      RingelNine.magnitude v 4 5 7
  have hrow_43 : lhs_43 < rhs_43 := by
    exact row_43 v hv
  have hlhs_43 : 0 < lhs_43 := by
    dsimp only [lhs_43]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_43 : 0 < rhs_43 := by
    dsimp only [rhs_43]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_44 : ℝ :=
    RingelNine.magnitude v 3 4 6 *
      RingelNine.magnitude v 4 7 8
  let rhs_44 : ℝ :=
    RingelNine.magnitude v 3 4 7 *
      RingelNine.magnitude v 4 6 8
  have hrow_44 : lhs_44 < rhs_44 := by
    exact row_44 v hv
  have hlhs_44 : 0 < lhs_44 := by
    dsimp only [lhs_44]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_44 : 0 < rhs_44 := by
    dsimp only [rhs_44]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_45 : ℝ :=
    RingelNine.magnitude v 0 3 8 *
      RingelNine.magnitude v 1 2 3
  let rhs_45 : ℝ :=
    RingelNine.magnitude v 0 1 3 *
      RingelNine.magnitude v 2 3 8
  have hrow_45 : lhs_45 < rhs_45 := by
    exact row_45 v hv
  have hlhs_45 : 0 < lhs_45 := by
    dsimp only [lhs_45]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_45 : 0 < rhs_45 := by
    dsimp only [rhs_45]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_46 : ℝ :=
    RingelNine.magnitude v 0 3 8 *
      RingelNine.magnitude v 2 3 4
  let rhs_46 : ℝ :=
    RingelNine.magnitude v 0 3 4 *
      RingelNine.magnitude v 2 3 8
  have hrow_46 : lhs_46 < rhs_46 := by
    exact row_46 v hv
  have hlhs_46 : 0 < lhs_46 := by
    dsimp only [lhs_46]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_46 : 0 < rhs_46 := by
    dsimp only [rhs_46]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_47 : ℝ :=
    RingelNine.magnitude v 0 3 6 *
      RingelNine.magnitude v 3 7 8
  let rhs_47 : ℝ :=
    RingelNine.magnitude v 0 3 8 *
      RingelNine.magnitude v 3 6 7
  have hrow_47 : lhs_47 < rhs_47 := by
    exact row_47 v hv
  have hlhs_47 : 0 < lhs_47 := by
    dsimp only [lhs_47]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_47 : 0 < rhs_47 := by
    dsimp only [rhs_47]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_48 : ℝ :=
    RingelNine.magnitude v 1 2 3 *
      RingelNine.magnitude v 3 4 8
  let rhs_48 : ℝ :=
    RingelNine.magnitude v 1 3 8 *
      RingelNine.magnitude v 2 3 4
  have hrow_48 : lhs_48 < rhs_48 := by
    exact row_48 v hv
  have hlhs_48 : 0 < lhs_48 := by
    dsimp only [lhs_48]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_48 : 0 < rhs_48 := by
    dsimp only [rhs_48]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_49 : ℝ :=
    RingelNine.magnitude v 1 2 3 *
      RingelNine.magnitude v 3 4 8
  let rhs_49 : ℝ :=
    RingelNine.magnitude v 1 3 8 *
      RingelNine.magnitude v 2 3 4
  have hrow_49 : lhs_49 < rhs_49 := by
    exact row_49 v hv
  have hlhs_49 : 0 < lhs_49 := by
    dsimp only [lhs_49]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_49 : 0 < rhs_49 := by
    dsimp only [rhs_49]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_50 : ℝ :=
    RingelNine.magnitude v 3 4 6 *
      RingelNine.magnitude v 3 5 8
  let rhs_50 : ℝ :=
    RingelNine.magnitude v 3 4 8 *
      RingelNine.magnitude v 3 5 6
  have hrow_50 : lhs_50 < rhs_50 := by
    exact row_50 v hv
  have hlhs_50 : 0 < lhs_50 := by
    dsimp only [lhs_50]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_50 : 0 < rhs_50 := by
    dsimp only [rhs_50]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_51 : ℝ :=
    RingelNine.magnitude v 0 2 5 *
      RingelNine.magnitude v 1 5 6
  let rhs_51 : ℝ :=
    RingelNine.magnitude v 0 5 6 *
      RingelNine.magnitude v 1 2 5
  have hrow_51 : lhs_51 < rhs_51 := by
    exact row_51 v hv
  have hlhs_51 : 0 < lhs_51 := by
    dsimp only [lhs_51]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_51 : 0 < rhs_51 := by
    dsimp only [rhs_51]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_52 : ℝ :=
    RingelNine.magnitude v 1 5 7 *
      RingelNine.magnitude v 2 5 8
  let rhs_52 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 5 7 8
  have hrow_52 : lhs_52 < rhs_52 := by
    exact row_52 v hv
  have hlhs_52 : 0 < lhs_52 := by
    dsimp only [lhs_52]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_52 : 0 < rhs_52 := by
    dsimp only [rhs_52]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_53 : ℝ :=
    RingelNine.magnitude v 1 5 7 *
      RingelNine.magnitude v 2 5 8
  let rhs_53 : ℝ :=
    RingelNine.magnitude v 1 2 5 *
      RingelNine.magnitude v 5 7 8
  have hrow_53 : lhs_53 < rhs_53 := by
    exact row_53 v hv
  have hlhs_53 : 0 < lhs_53 := by
    dsimp only [lhs_53]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_53 : 0 < rhs_53 := by
    dsimp only [rhs_53]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_54 : ℝ :=
    RingelNine.magnitude v 2 4 5 *
      RingelNine.magnitude v 3 5 6
  let rhs_54 : ℝ :=
    RingelNine.magnitude v 2 3 5 *
      RingelNine.magnitude v 4 5 6
  have hrow_54 : lhs_54 < rhs_54 := by
    exact row_54 v hv
  have hlhs_54 : 0 < lhs_54 := by
    dsimp only [lhs_54]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_54 : 0 < rhs_54 := by
    dsimp only [rhs_54]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_55 : ℝ :=
    RingelNine.magnitude v 1 7 8 *
      RingelNine.magnitude v 2 5 7
  let rhs_55 : ℝ :=
    RingelNine.magnitude v 1 5 7 *
      RingelNine.magnitude v 2 7 8
  have hrow_55 : lhs_55 < rhs_55 := by
    exact row_55 v hv
  have hlhs_55 : 0 < lhs_55 := by
    dsimp only [lhs_55]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_55 : 0 < rhs_55 := by
    dsimp only [rhs_55]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_56 : ℝ :=
    RingelNine.magnitude v 1 5 7 *
      RingelNine.magnitude v 2 3 7
  let rhs_56 : ℝ :=
    RingelNine.magnitude v 1 3 7 *
      RingelNine.magnitude v 2 5 7
  have hrow_56 : lhs_56 < rhs_56 := by
    exact row_56 v hv
  have hlhs_56 : 0 < lhs_56 := by
    dsimp only [lhs_56]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_56 : 0 < rhs_56 := by
    dsimp only [rhs_56]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_57 : ℝ :=
    RingelNine.magnitude v 1 6 7 *
      RingelNine.magnitude v 4 7 8
  let rhs_57 : ℝ :=
    RingelNine.magnitude v 1 4 7 *
      RingelNine.magnitude v 6 7 8
  have hrow_57 : lhs_57 < rhs_57 := by
    exact row_57 v hv
  have hlhs_57 : 0 < lhs_57 := by
    dsimp only [lhs_57]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_57 : 0 < rhs_57 := by
    dsimp only [rhs_57]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_58 : ℝ :=
    RingelNine.magnitude v 3 4 7 *
      RingelNine.magnitude v 5 6 7
  let rhs_58 : ℝ :=
    RingelNine.magnitude v 3 6 7 *
      RingelNine.magnitude v 4 5 7
  have hrow_58 : lhs_58 < rhs_58 := by
    exact row_58 v hv
  have hlhs_58 : 0 < lhs_58 := by
    dsimp only [lhs_58]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  have hrhs_58 : 0 < rhs_58 := by
    dsimp only [rhs_58]
    exact mul_pos
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
      (hv.normalizedBracket_pos (by decide) (by decide) (by decide))
  let lhs_product_00 : ℝ := lhs_00
  let rhs_product_00 : ℝ := rhs_00
  have hproduct_00 : lhs_product_00 < rhs_product_00 := hrow_00
  have hrhs_product_00 : 0 < rhs_product_00 := hrhs_00
  let lhs_product_01 : ℝ :=
    lhs_product_00 * lhs_01
  let rhs_product_01 : ℝ :=
    rhs_product_00 * rhs_01
  have hproduct_01 :
      lhs_product_01 < rhs_product_01 := by
    dsimp only [lhs_product_01, rhs_product_01]
    exact mul_lt_mul hproduct_00
      (le_of_lt hrow_01) hlhs_01
      (le_of_lt hrhs_product_00)
  have hrhs_product_01 : 0 < rhs_product_01 := by
    dsimp only [rhs_product_01]
    exact mul_pos hrhs_product_00 hrhs_01
  let lhs_product_02 : ℝ :=
    lhs_product_01 * lhs_02
  let rhs_product_02 : ℝ :=
    rhs_product_01 * rhs_02
  have hproduct_02 :
      lhs_product_02 < rhs_product_02 := by
    dsimp only [lhs_product_02, rhs_product_02]
    exact mul_lt_mul hproduct_01
      (le_of_lt hrow_02) hlhs_02
      (le_of_lt hrhs_product_01)
  have hrhs_product_02 : 0 < rhs_product_02 := by
    dsimp only [rhs_product_02]
    exact mul_pos hrhs_product_01 hrhs_02
  let lhs_product_03 : ℝ :=
    lhs_product_02 * lhs_03
  let rhs_product_03 : ℝ :=
    rhs_product_02 * rhs_03
  have hproduct_03 :
      lhs_product_03 < rhs_product_03 := by
    dsimp only [lhs_product_03, rhs_product_03]
    exact mul_lt_mul hproduct_02
      (le_of_lt hrow_03) hlhs_03
      (le_of_lt hrhs_product_02)
  have hrhs_product_03 : 0 < rhs_product_03 := by
    dsimp only [rhs_product_03]
    exact mul_pos hrhs_product_02 hrhs_03
  let lhs_product_04 : ℝ :=
    lhs_product_03 * lhs_04
  let rhs_product_04 : ℝ :=
    rhs_product_03 * rhs_04
  have hproduct_04 :
      lhs_product_04 < rhs_product_04 := by
    dsimp only [lhs_product_04, rhs_product_04]
    exact mul_lt_mul hproduct_03
      (le_of_lt hrow_04) hlhs_04
      (le_of_lt hrhs_product_03)
  have hrhs_product_04 : 0 < rhs_product_04 := by
    dsimp only [rhs_product_04]
    exact mul_pos hrhs_product_03 hrhs_04
  let lhs_product_05 : ℝ :=
    lhs_product_04 * lhs_05
  let rhs_product_05 : ℝ :=
    rhs_product_04 * rhs_05
  have hproduct_05 :
      lhs_product_05 < rhs_product_05 := by
    dsimp only [lhs_product_05, rhs_product_05]
    exact mul_lt_mul hproduct_04
      (le_of_lt hrow_05) hlhs_05
      (le_of_lt hrhs_product_04)
  have hrhs_product_05 : 0 < rhs_product_05 := by
    dsimp only [rhs_product_05]
    exact mul_pos hrhs_product_04 hrhs_05
  let lhs_product_06 : ℝ :=
    lhs_product_05 * lhs_06
  let rhs_product_06 : ℝ :=
    rhs_product_05 * rhs_06
  have hproduct_06 :
      lhs_product_06 < rhs_product_06 := by
    dsimp only [lhs_product_06, rhs_product_06]
    exact mul_lt_mul hproduct_05
      (le_of_lt hrow_06) hlhs_06
      (le_of_lt hrhs_product_05)
  have hrhs_product_06 : 0 < rhs_product_06 := by
    dsimp only [rhs_product_06]
    exact mul_pos hrhs_product_05 hrhs_06
  let lhs_product_07 : ℝ :=
    lhs_product_06 * lhs_07
  let rhs_product_07 : ℝ :=
    rhs_product_06 * rhs_07
  have hproduct_07 :
      lhs_product_07 < rhs_product_07 := by
    dsimp only [lhs_product_07, rhs_product_07]
    exact mul_lt_mul hproduct_06
      (le_of_lt hrow_07) hlhs_07
      (le_of_lt hrhs_product_06)
  have hrhs_product_07 : 0 < rhs_product_07 := by
    dsimp only [rhs_product_07]
    exact mul_pos hrhs_product_06 hrhs_07
  let lhs_product_08 : ℝ :=
    lhs_product_07 * lhs_08
  let rhs_product_08 : ℝ :=
    rhs_product_07 * rhs_08
  have hproduct_08 :
      lhs_product_08 < rhs_product_08 := by
    dsimp only [lhs_product_08, rhs_product_08]
    exact mul_lt_mul hproduct_07
      (le_of_lt hrow_08) hlhs_08
      (le_of_lt hrhs_product_07)
  have hrhs_product_08 : 0 < rhs_product_08 := by
    dsimp only [rhs_product_08]
    exact mul_pos hrhs_product_07 hrhs_08
  let lhs_product_09 : ℝ :=
    lhs_product_08 * lhs_09
  let rhs_product_09 : ℝ :=
    rhs_product_08 * rhs_09
  have hproduct_09 :
      lhs_product_09 < rhs_product_09 := by
    dsimp only [lhs_product_09, rhs_product_09]
    exact mul_lt_mul hproduct_08
      (le_of_lt hrow_09) hlhs_09
      (le_of_lt hrhs_product_08)
  have hrhs_product_09 : 0 < rhs_product_09 := by
    dsimp only [rhs_product_09]
    exact mul_pos hrhs_product_08 hrhs_09
  let lhs_product_10 : ℝ :=
    lhs_product_09 * lhs_10
  let rhs_product_10 : ℝ :=
    rhs_product_09 * rhs_10
  have hproduct_10 :
      lhs_product_10 < rhs_product_10 := by
    dsimp only [lhs_product_10, rhs_product_10]
    exact mul_lt_mul hproduct_09
      (le_of_lt hrow_10) hlhs_10
      (le_of_lt hrhs_product_09)
  have hrhs_product_10 : 0 < rhs_product_10 := by
    dsimp only [rhs_product_10]
    exact mul_pos hrhs_product_09 hrhs_10
  let lhs_product_11 : ℝ :=
    lhs_product_10 * lhs_11
  let rhs_product_11 : ℝ :=
    rhs_product_10 * rhs_11
  have hproduct_11 :
      lhs_product_11 < rhs_product_11 := by
    dsimp only [lhs_product_11, rhs_product_11]
    exact mul_lt_mul hproduct_10
      (le_of_lt hrow_11) hlhs_11
      (le_of_lt hrhs_product_10)
  have hrhs_product_11 : 0 < rhs_product_11 := by
    dsimp only [rhs_product_11]
    exact mul_pos hrhs_product_10 hrhs_11
  let lhs_product_12 : ℝ :=
    lhs_product_11 * lhs_12
  let rhs_product_12 : ℝ :=
    rhs_product_11 * rhs_12
  have hproduct_12 :
      lhs_product_12 < rhs_product_12 := by
    dsimp only [lhs_product_12, rhs_product_12]
    exact mul_lt_mul hproduct_11
      (le_of_lt hrow_12) hlhs_12
      (le_of_lt hrhs_product_11)
  have hrhs_product_12 : 0 < rhs_product_12 := by
    dsimp only [rhs_product_12]
    exact mul_pos hrhs_product_11 hrhs_12
  let lhs_product_13 : ℝ :=
    lhs_product_12 * lhs_13
  let rhs_product_13 : ℝ :=
    rhs_product_12 * rhs_13
  have hproduct_13 :
      lhs_product_13 < rhs_product_13 := by
    dsimp only [lhs_product_13, rhs_product_13]
    exact mul_lt_mul hproduct_12
      (le_of_lt hrow_13) hlhs_13
      (le_of_lt hrhs_product_12)
  have hrhs_product_13 : 0 < rhs_product_13 := by
    dsimp only [rhs_product_13]
    exact mul_pos hrhs_product_12 hrhs_13
  let lhs_product_14 : ℝ :=
    lhs_product_13 * lhs_14
  let rhs_product_14 : ℝ :=
    rhs_product_13 * rhs_14
  have hproduct_14 :
      lhs_product_14 < rhs_product_14 := by
    dsimp only [lhs_product_14, rhs_product_14]
    exact mul_lt_mul hproduct_13
      (le_of_lt hrow_14) hlhs_14
      (le_of_lt hrhs_product_13)
  have hrhs_product_14 : 0 < rhs_product_14 := by
    dsimp only [rhs_product_14]
    exact mul_pos hrhs_product_13 hrhs_14
  let lhs_product_15 : ℝ :=
    lhs_product_14 * lhs_15
  let rhs_product_15 : ℝ :=
    rhs_product_14 * rhs_15
  have hproduct_15 :
      lhs_product_15 < rhs_product_15 := by
    dsimp only [lhs_product_15, rhs_product_15]
    exact mul_lt_mul hproduct_14
      (le_of_lt hrow_15) hlhs_15
      (le_of_lt hrhs_product_14)
  have hrhs_product_15 : 0 < rhs_product_15 := by
    dsimp only [rhs_product_15]
    exact mul_pos hrhs_product_14 hrhs_15
  let lhs_product_16 : ℝ :=
    lhs_product_15 * lhs_16
  let rhs_product_16 : ℝ :=
    rhs_product_15 * rhs_16
  have hproduct_16 :
      lhs_product_16 < rhs_product_16 := by
    dsimp only [lhs_product_16, rhs_product_16]
    exact mul_lt_mul hproduct_15
      (le_of_lt hrow_16) hlhs_16
      (le_of_lt hrhs_product_15)
  have hrhs_product_16 : 0 < rhs_product_16 := by
    dsimp only [rhs_product_16]
    exact mul_pos hrhs_product_15 hrhs_16
  let lhs_product_17 : ℝ :=
    lhs_product_16 * lhs_17
  let rhs_product_17 : ℝ :=
    rhs_product_16 * rhs_17
  have hproduct_17 :
      lhs_product_17 < rhs_product_17 := by
    dsimp only [lhs_product_17, rhs_product_17]
    exact mul_lt_mul hproduct_16
      (le_of_lt hrow_17) hlhs_17
      (le_of_lt hrhs_product_16)
  have hrhs_product_17 : 0 < rhs_product_17 := by
    dsimp only [rhs_product_17]
    exact mul_pos hrhs_product_16 hrhs_17
  let lhs_product_18 : ℝ :=
    lhs_product_17 * lhs_18
  let rhs_product_18 : ℝ :=
    rhs_product_17 * rhs_18
  have hproduct_18 :
      lhs_product_18 < rhs_product_18 := by
    dsimp only [lhs_product_18, rhs_product_18]
    exact mul_lt_mul hproduct_17
      (le_of_lt hrow_18) hlhs_18
      (le_of_lt hrhs_product_17)
  have hrhs_product_18 : 0 < rhs_product_18 := by
    dsimp only [rhs_product_18]
    exact mul_pos hrhs_product_17 hrhs_18
  let lhs_product_19 : ℝ :=
    lhs_product_18 * lhs_19
  let rhs_product_19 : ℝ :=
    rhs_product_18 * rhs_19
  have hproduct_19 :
      lhs_product_19 < rhs_product_19 := by
    dsimp only [lhs_product_19, rhs_product_19]
    exact mul_lt_mul hproduct_18
      (le_of_lt hrow_19) hlhs_19
      (le_of_lt hrhs_product_18)
  have hrhs_product_19 : 0 < rhs_product_19 := by
    dsimp only [rhs_product_19]
    exact mul_pos hrhs_product_18 hrhs_19
  let lhs_product_20 : ℝ :=
    lhs_product_19 * lhs_20
  let rhs_product_20 : ℝ :=
    rhs_product_19 * rhs_20
  have hproduct_20 :
      lhs_product_20 < rhs_product_20 := by
    dsimp only [lhs_product_20, rhs_product_20]
    exact mul_lt_mul hproduct_19
      (le_of_lt hrow_20) hlhs_20
      (le_of_lt hrhs_product_19)
  have hrhs_product_20 : 0 < rhs_product_20 := by
    dsimp only [rhs_product_20]
    exact mul_pos hrhs_product_19 hrhs_20
  let lhs_product_21 : ℝ :=
    lhs_product_20 * lhs_21
  let rhs_product_21 : ℝ :=
    rhs_product_20 * rhs_21
  have hproduct_21 :
      lhs_product_21 < rhs_product_21 := by
    dsimp only [lhs_product_21, rhs_product_21]
    exact mul_lt_mul hproduct_20
      (le_of_lt hrow_21) hlhs_21
      (le_of_lt hrhs_product_20)
  have hrhs_product_21 : 0 < rhs_product_21 := by
    dsimp only [rhs_product_21]
    exact mul_pos hrhs_product_20 hrhs_21
  let lhs_product_22 : ℝ :=
    lhs_product_21 * lhs_22
  let rhs_product_22 : ℝ :=
    rhs_product_21 * rhs_22
  have hproduct_22 :
      lhs_product_22 < rhs_product_22 := by
    dsimp only [lhs_product_22, rhs_product_22]
    exact mul_lt_mul hproduct_21
      (le_of_lt hrow_22) hlhs_22
      (le_of_lt hrhs_product_21)
  have hrhs_product_22 : 0 < rhs_product_22 := by
    dsimp only [rhs_product_22]
    exact mul_pos hrhs_product_21 hrhs_22
  let lhs_product_23 : ℝ :=
    lhs_product_22 * lhs_23
  let rhs_product_23 : ℝ :=
    rhs_product_22 * rhs_23
  have hproduct_23 :
      lhs_product_23 < rhs_product_23 := by
    dsimp only [lhs_product_23, rhs_product_23]
    exact mul_lt_mul hproduct_22
      (le_of_lt hrow_23) hlhs_23
      (le_of_lt hrhs_product_22)
  have hrhs_product_23 : 0 < rhs_product_23 := by
    dsimp only [rhs_product_23]
    exact mul_pos hrhs_product_22 hrhs_23
  let lhs_product_24 : ℝ :=
    lhs_product_23 * lhs_24
  let rhs_product_24 : ℝ :=
    rhs_product_23 * rhs_24
  have hproduct_24 :
      lhs_product_24 < rhs_product_24 := by
    dsimp only [lhs_product_24, rhs_product_24]
    exact mul_lt_mul hproduct_23
      (le_of_lt hrow_24) hlhs_24
      (le_of_lt hrhs_product_23)
  have hrhs_product_24 : 0 < rhs_product_24 := by
    dsimp only [rhs_product_24]
    exact mul_pos hrhs_product_23 hrhs_24
  let lhs_product_25 : ℝ :=
    lhs_product_24 * lhs_25
  let rhs_product_25 : ℝ :=
    rhs_product_24 * rhs_25
  have hproduct_25 :
      lhs_product_25 < rhs_product_25 := by
    dsimp only [lhs_product_25, rhs_product_25]
    exact mul_lt_mul hproduct_24
      (le_of_lt hrow_25) hlhs_25
      (le_of_lt hrhs_product_24)
  have hrhs_product_25 : 0 < rhs_product_25 := by
    dsimp only [rhs_product_25]
    exact mul_pos hrhs_product_24 hrhs_25
  let lhs_product_26 : ℝ :=
    lhs_product_25 * lhs_26
  let rhs_product_26 : ℝ :=
    rhs_product_25 * rhs_26
  have hproduct_26 :
      lhs_product_26 < rhs_product_26 := by
    dsimp only [lhs_product_26, rhs_product_26]
    exact mul_lt_mul hproduct_25
      (le_of_lt hrow_26) hlhs_26
      (le_of_lt hrhs_product_25)
  have hrhs_product_26 : 0 < rhs_product_26 := by
    dsimp only [rhs_product_26]
    exact mul_pos hrhs_product_25 hrhs_26
  let lhs_product_27 : ℝ :=
    lhs_product_26 * lhs_27
  let rhs_product_27 : ℝ :=
    rhs_product_26 * rhs_27
  have hproduct_27 :
      lhs_product_27 < rhs_product_27 := by
    dsimp only [lhs_product_27, rhs_product_27]
    exact mul_lt_mul hproduct_26
      (le_of_lt hrow_27) hlhs_27
      (le_of_lt hrhs_product_26)
  have hrhs_product_27 : 0 < rhs_product_27 := by
    dsimp only [rhs_product_27]
    exact mul_pos hrhs_product_26 hrhs_27
  let lhs_product_28 : ℝ :=
    lhs_product_27 * lhs_28
  let rhs_product_28 : ℝ :=
    rhs_product_27 * rhs_28
  have hproduct_28 :
      lhs_product_28 < rhs_product_28 := by
    dsimp only [lhs_product_28, rhs_product_28]
    exact mul_lt_mul hproduct_27
      (le_of_lt hrow_28) hlhs_28
      (le_of_lt hrhs_product_27)
  have hrhs_product_28 : 0 < rhs_product_28 := by
    dsimp only [rhs_product_28]
    exact mul_pos hrhs_product_27 hrhs_28
  let lhs_product_29 : ℝ :=
    lhs_product_28 * lhs_29
  let rhs_product_29 : ℝ :=
    rhs_product_28 * rhs_29
  have hproduct_29 :
      lhs_product_29 < rhs_product_29 := by
    dsimp only [lhs_product_29, rhs_product_29]
    exact mul_lt_mul hproduct_28
      (le_of_lt hrow_29) hlhs_29
      (le_of_lt hrhs_product_28)
  have hrhs_product_29 : 0 < rhs_product_29 := by
    dsimp only [rhs_product_29]
    exact mul_pos hrhs_product_28 hrhs_29
  let lhs_product_30 : ℝ :=
    lhs_product_29 * lhs_30
  let rhs_product_30 : ℝ :=
    rhs_product_29 * rhs_30
  have hproduct_30 :
      lhs_product_30 < rhs_product_30 := by
    dsimp only [lhs_product_30, rhs_product_30]
    exact mul_lt_mul hproduct_29
      (le_of_lt hrow_30) hlhs_30
      (le_of_lt hrhs_product_29)
  have hrhs_product_30 : 0 < rhs_product_30 := by
    dsimp only [rhs_product_30]
    exact mul_pos hrhs_product_29 hrhs_30
  let lhs_product_31 : ℝ :=
    lhs_product_30 * lhs_31
  let rhs_product_31 : ℝ :=
    rhs_product_30 * rhs_31
  have hproduct_31 :
      lhs_product_31 < rhs_product_31 := by
    dsimp only [lhs_product_31, rhs_product_31]
    exact mul_lt_mul hproduct_30
      (le_of_lt hrow_31) hlhs_31
      (le_of_lt hrhs_product_30)
  have hrhs_product_31 : 0 < rhs_product_31 := by
    dsimp only [rhs_product_31]
    exact mul_pos hrhs_product_30 hrhs_31
  let lhs_product_32 : ℝ :=
    lhs_product_31 * lhs_32
  let rhs_product_32 : ℝ :=
    rhs_product_31 * rhs_32
  have hproduct_32 :
      lhs_product_32 < rhs_product_32 := by
    dsimp only [lhs_product_32, rhs_product_32]
    exact mul_lt_mul hproduct_31
      (le_of_lt hrow_32) hlhs_32
      (le_of_lt hrhs_product_31)
  have hrhs_product_32 : 0 < rhs_product_32 := by
    dsimp only [rhs_product_32]
    exact mul_pos hrhs_product_31 hrhs_32
  let lhs_product_33 : ℝ :=
    lhs_product_32 * lhs_33
  let rhs_product_33 : ℝ :=
    rhs_product_32 * rhs_33
  have hproduct_33 :
      lhs_product_33 < rhs_product_33 := by
    dsimp only [lhs_product_33, rhs_product_33]
    exact mul_lt_mul hproduct_32
      (le_of_lt hrow_33) hlhs_33
      (le_of_lt hrhs_product_32)
  have hrhs_product_33 : 0 < rhs_product_33 := by
    dsimp only [rhs_product_33]
    exact mul_pos hrhs_product_32 hrhs_33
  let lhs_product_34 : ℝ :=
    lhs_product_33 * lhs_34
  let rhs_product_34 : ℝ :=
    rhs_product_33 * rhs_34
  have hproduct_34 :
      lhs_product_34 < rhs_product_34 := by
    dsimp only [lhs_product_34, rhs_product_34]
    exact mul_lt_mul hproduct_33
      (le_of_lt hrow_34) hlhs_34
      (le_of_lt hrhs_product_33)
  have hrhs_product_34 : 0 < rhs_product_34 := by
    dsimp only [rhs_product_34]
    exact mul_pos hrhs_product_33 hrhs_34
  let lhs_product_35 : ℝ :=
    lhs_product_34 * lhs_35
  let rhs_product_35 : ℝ :=
    rhs_product_34 * rhs_35
  have hproduct_35 :
      lhs_product_35 < rhs_product_35 := by
    dsimp only [lhs_product_35, rhs_product_35]
    exact mul_lt_mul hproduct_34
      (le_of_lt hrow_35) hlhs_35
      (le_of_lt hrhs_product_34)
  have hrhs_product_35 : 0 < rhs_product_35 := by
    dsimp only [rhs_product_35]
    exact mul_pos hrhs_product_34 hrhs_35
  let lhs_product_36 : ℝ :=
    lhs_product_35 * lhs_36
  let rhs_product_36 : ℝ :=
    rhs_product_35 * rhs_36
  have hproduct_36 :
      lhs_product_36 < rhs_product_36 := by
    dsimp only [lhs_product_36, rhs_product_36]
    exact mul_lt_mul hproduct_35
      (le_of_lt hrow_36) hlhs_36
      (le_of_lt hrhs_product_35)
  have hrhs_product_36 : 0 < rhs_product_36 := by
    dsimp only [rhs_product_36]
    exact mul_pos hrhs_product_35 hrhs_36
  let lhs_product_37 : ℝ :=
    lhs_product_36 * lhs_37
  let rhs_product_37 : ℝ :=
    rhs_product_36 * rhs_37
  have hproduct_37 :
      lhs_product_37 < rhs_product_37 := by
    dsimp only [lhs_product_37, rhs_product_37]
    exact mul_lt_mul hproduct_36
      (le_of_lt hrow_37) hlhs_37
      (le_of_lt hrhs_product_36)
  have hrhs_product_37 : 0 < rhs_product_37 := by
    dsimp only [rhs_product_37]
    exact mul_pos hrhs_product_36 hrhs_37
  let lhs_product_38 : ℝ :=
    lhs_product_37 * lhs_38
  let rhs_product_38 : ℝ :=
    rhs_product_37 * rhs_38
  have hproduct_38 :
      lhs_product_38 < rhs_product_38 := by
    dsimp only [lhs_product_38, rhs_product_38]
    exact mul_lt_mul hproduct_37
      (le_of_lt hrow_38) hlhs_38
      (le_of_lt hrhs_product_37)
  have hrhs_product_38 : 0 < rhs_product_38 := by
    dsimp only [rhs_product_38]
    exact mul_pos hrhs_product_37 hrhs_38
  let lhs_product_39 : ℝ :=
    lhs_product_38 * lhs_39
  let rhs_product_39 : ℝ :=
    rhs_product_38 * rhs_39
  have hproduct_39 :
      lhs_product_39 < rhs_product_39 := by
    dsimp only [lhs_product_39, rhs_product_39]
    exact mul_lt_mul hproduct_38
      (le_of_lt hrow_39) hlhs_39
      (le_of_lt hrhs_product_38)
  have hrhs_product_39 : 0 < rhs_product_39 := by
    dsimp only [rhs_product_39]
    exact mul_pos hrhs_product_38 hrhs_39
  let lhs_product_40 : ℝ :=
    lhs_product_39 * lhs_40
  let rhs_product_40 : ℝ :=
    rhs_product_39 * rhs_40
  have hproduct_40 :
      lhs_product_40 < rhs_product_40 := by
    dsimp only [lhs_product_40, rhs_product_40]
    exact mul_lt_mul hproduct_39
      (le_of_lt hrow_40) hlhs_40
      (le_of_lt hrhs_product_39)
  have hrhs_product_40 : 0 < rhs_product_40 := by
    dsimp only [rhs_product_40]
    exact mul_pos hrhs_product_39 hrhs_40
  let lhs_product_41 : ℝ :=
    lhs_product_40 * lhs_41
  let rhs_product_41 : ℝ :=
    rhs_product_40 * rhs_41
  have hproduct_41 :
      lhs_product_41 < rhs_product_41 := by
    dsimp only [lhs_product_41, rhs_product_41]
    exact mul_lt_mul hproduct_40
      (le_of_lt hrow_41) hlhs_41
      (le_of_lt hrhs_product_40)
  have hrhs_product_41 : 0 < rhs_product_41 := by
    dsimp only [rhs_product_41]
    exact mul_pos hrhs_product_40 hrhs_41
  let lhs_product_42 : ℝ :=
    lhs_product_41 * lhs_42
  let rhs_product_42 : ℝ :=
    rhs_product_41 * rhs_42
  have hproduct_42 :
      lhs_product_42 < rhs_product_42 := by
    dsimp only [lhs_product_42, rhs_product_42]
    exact mul_lt_mul hproduct_41
      (le_of_lt hrow_42) hlhs_42
      (le_of_lt hrhs_product_41)
  have hrhs_product_42 : 0 < rhs_product_42 := by
    dsimp only [rhs_product_42]
    exact mul_pos hrhs_product_41 hrhs_42
  let lhs_product_43 : ℝ :=
    lhs_product_42 * lhs_43
  let rhs_product_43 : ℝ :=
    rhs_product_42 * rhs_43
  have hproduct_43 :
      lhs_product_43 < rhs_product_43 := by
    dsimp only [lhs_product_43, rhs_product_43]
    exact mul_lt_mul hproduct_42
      (le_of_lt hrow_43) hlhs_43
      (le_of_lt hrhs_product_42)
  have hrhs_product_43 : 0 < rhs_product_43 := by
    dsimp only [rhs_product_43]
    exact mul_pos hrhs_product_42 hrhs_43
  let lhs_product_44 : ℝ :=
    lhs_product_43 * lhs_44
  let rhs_product_44 : ℝ :=
    rhs_product_43 * rhs_44
  have hproduct_44 :
      lhs_product_44 < rhs_product_44 := by
    dsimp only [lhs_product_44, rhs_product_44]
    exact mul_lt_mul hproduct_43
      (le_of_lt hrow_44) hlhs_44
      (le_of_lt hrhs_product_43)
  have hrhs_product_44 : 0 < rhs_product_44 := by
    dsimp only [rhs_product_44]
    exact mul_pos hrhs_product_43 hrhs_44
  let lhs_product_45 : ℝ :=
    lhs_product_44 * lhs_45
  let rhs_product_45 : ℝ :=
    rhs_product_44 * rhs_45
  have hproduct_45 :
      lhs_product_45 < rhs_product_45 := by
    dsimp only [lhs_product_45, rhs_product_45]
    exact mul_lt_mul hproduct_44
      (le_of_lt hrow_45) hlhs_45
      (le_of_lt hrhs_product_44)
  have hrhs_product_45 : 0 < rhs_product_45 := by
    dsimp only [rhs_product_45]
    exact mul_pos hrhs_product_44 hrhs_45
  let lhs_product_46 : ℝ :=
    lhs_product_45 * lhs_46
  let rhs_product_46 : ℝ :=
    rhs_product_45 * rhs_46
  have hproduct_46 :
      lhs_product_46 < rhs_product_46 := by
    dsimp only [lhs_product_46, rhs_product_46]
    exact mul_lt_mul hproduct_45
      (le_of_lt hrow_46) hlhs_46
      (le_of_lt hrhs_product_45)
  have hrhs_product_46 : 0 < rhs_product_46 := by
    dsimp only [rhs_product_46]
    exact mul_pos hrhs_product_45 hrhs_46
  let lhs_product_47 : ℝ :=
    lhs_product_46 * lhs_47
  let rhs_product_47 : ℝ :=
    rhs_product_46 * rhs_47
  have hproduct_47 :
      lhs_product_47 < rhs_product_47 := by
    dsimp only [lhs_product_47, rhs_product_47]
    exact mul_lt_mul hproduct_46
      (le_of_lt hrow_47) hlhs_47
      (le_of_lt hrhs_product_46)
  have hrhs_product_47 : 0 < rhs_product_47 := by
    dsimp only [rhs_product_47]
    exact mul_pos hrhs_product_46 hrhs_47
  let lhs_product_48 : ℝ :=
    lhs_product_47 * lhs_48
  let rhs_product_48 : ℝ :=
    rhs_product_47 * rhs_48
  have hproduct_48 :
      lhs_product_48 < rhs_product_48 := by
    dsimp only [lhs_product_48, rhs_product_48]
    exact mul_lt_mul hproduct_47
      (le_of_lt hrow_48) hlhs_48
      (le_of_lt hrhs_product_47)
  have hrhs_product_48 : 0 < rhs_product_48 := by
    dsimp only [rhs_product_48]
    exact mul_pos hrhs_product_47 hrhs_48
  let lhs_product_49 : ℝ :=
    lhs_product_48 * lhs_49
  let rhs_product_49 : ℝ :=
    rhs_product_48 * rhs_49
  have hproduct_49 :
      lhs_product_49 < rhs_product_49 := by
    dsimp only [lhs_product_49, rhs_product_49]
    exact mul_lt_mul hproduct_48
      (le_of_lt hrow_49) hlhs_49
      (le_of_lt hrhs_product_48)
  have hrhs_product_49 : 0 < rhs_product_49 := by
    dsimp only [rhs_product_49]
    exact mul_pos hrhs_product_48 hrhs_49
  let lhs_product_50 : ℝ :=
    lhs_product_49 * lhs_50
  let rhs_product_50 : ℝ :=
    rhs_product_49 * rhs_50
  have hproduct_50 :
      lhs_product_50 < rhs_product_50 := by
    dsimp only [lhs_product_50, rhs_product_50]
    exact mul_lt_mul hproduct_49
      (le_of_lt hrow_50) hlhs_50
      (le_of_lt hrhs_product_49)
  have hrhs_product_50 : 0 < rhs_product_50 := by
    dsimp only [rhs_product_50]
    exact mul_pos hrhs_product_49 hrhs_50
  let lhs_product_51 : ℝ :=
    lhs_product_50 * lhs_51
  let rhs_product_51 : ℝ :=
    rhs_product_50 * rhs_51
  have hproduct_51 :
      lhs_product_51 < rhs_product_51 := by
    dsimp only [lhs_product_51, rhs_product_51]
    exact mul_lt_mul hproduct_50
      (le_of_lt hrow_51) hlhs_51
      (le_of_lt hrhs_product_50)
  have hrhs_product_51 : 0 < rhs_product_51 := by
    dsimp only [rhs_product_51]
    exact mul_pos hrhs_product_50 hrhs_51
  let lhs_product_52 : ℝ :=
    lhs_product_51 * lhs_52
  let rhs_product_52 : ℝ :=
    rhs_product_51 * rhs_52
  have hproduct_52 :
      lhs_product_52 < rhs_product_52 := by
    dsimp only [lhs_product_52, rhs_product_52]
    exact mul_lt_mul hproduct_51
      (le_of_lt hrow_52) hlhs_52
      (le_of_lt hrhs_product_51)
  have hrhs_product_52 : 0 < rhs_product_52 := by
    dsimp only [rhs_product_52]
    exact mul_pos hrhs_product_51 hrhs_52
  let lhs_product_53 : ℝ :=
    lhs_product_52 * lhs_53
  let rhs_product_53 : ℝ :=
    rhs_product_52 * rhs_53
  have hproduct_53 :
      lhs_product_53 < rhs_product_53 := by
    dsimp only [lhs_product_53, rhs_product_53]
    exact mul_lt_mul hproduct_52
      (le_of_lt hrow_53) hlhs_53
      (le_of_lt hrhs_product_52)
  have hrhs_product_53 : 0 < rhs_product_53 := by
    dsimp only [rhs_product_53]
    exact mul_pos hrhs_product_52 hrhs_53
  let lhs_product_54 : ℝ :=
    lhs_product_53 * lhs_54
  let rhs_product_54 : ℝ :=
    rhs_product_53 * rhs_54
  have hproduct_54 :
      lhs_product_54 < rhs_product_54 := by
    dsimp only [lhs_product_54, rhs_product_54]
    exact mul_lt_mul hproduct_53
      (le_of_lt hrow_54) hlhs_54
      (le_of_lt hrhs_product_53)
  have hrhs_product_54 : 0 < rhs_product_54 := by
    dsimp only [rhs_product_54]
    exact mul_pos hrhs_product_53 hrhs_54
  let lhs_product_55 : ℝ :=
    lhs_product_54 * lhs_55
  let rhs_product_55 : ℝ :=
    rhs_product_54 * rhs_55
  have hproduct_55 :
      lhs_product_55 < rhs_product_55 := by
    dsimp only [lhs_product_55, rhs_product_55]
    exact mul_lt_mul hproduct_54
      (le_of_lt hrow_55) hlhs_55
      (le_of_lt hrhs_product_54)
  have hrhs_product_55 : 0 < rhs_product_55 := by
    dsimp only [rhs_product_55]
    exact mul_pos hrhs_product_54 hrhs_55
  let lhs_product_56 : ℝ :=
    lhs_product_55 * lhs_56
  let rhs_product_56 : ℝ :=
    rhs_product_55 * rhs_56
  have hproduct_56 :
      lhs_product_56 < rhs_product_56 := by
    dsimp only [lhs_product_56, rhs_product_56]
    exact mul_lt_mul hproduct_55
      (le_of_lt hrow_56) hlhs_56
      (le_of_lt hrhs_product_55)
  have hrhs_product_56 : 0 < rhs_product_56 := by
    dsimp only [rhs_product_56]
    exact mul_pos hrhs_product_55 hrhs_56
  let lhs_product_57 : ℝ :=
    lhs_product_56 * lhs_57
  let rhs_product_57 : ℝ :=
    rhs_product_56 * rhs_57
  have hproduct_57 :
      lhs_product_57 < rhs_product_57 := by
    dsimp only [lhs_product_57, rhs_product_57]
    exact mul_lt_mul hproduct_56
      (le_of_lt hrow_57) hlhs_57
      (le_of_lt hrhs_product_56)
  have hrhs_product_57 : 0 < rhs_product_57 := by
    dsimp only [rhs_product_57]
    exact mul_pos hrhs_product_56 hrhs_57
  let lhs_product_58 : ℝ :=
    lhs_product_57 * lhs_58
  let rhs_product_58 : ℝ :=
    rhs_product_57 * rhs_58
  have hproduct_58 :
      lhs_product_58 < rhs_product_58 := by
    dsimp only [lhs_product_58, rhs_product_58]
    exact mul_lt_mul hproduct_57
      (le_of_lt hrow_58) hlhs_58
      (le_of_lt hrhs_product_57)
  have hrhs_product_58 : 0 < rhs_product_58 := by
    dsimp only [rhs_product_58]
    exact mul_pos hrhs_product_57 hrhs_58
  have hbalanced : lhs_product_58 = rhs_product_58 := by
    dsimp only [
      lhs_product_58,
      rhs_product_58,
      lhs_product_57,
      rhs_product_57,
      lhs_product_56,
      rhs_product_56,
      lhs_product_55,
      rhs_product_55,
      lhs_product_54,
      rhs_product_54,
      lhs_product_53,
      rhs_product_53,
      lhs_product_52,
      rhs_product_52,
      lhs_product_51,
      rhs_product_51,
      lhs_product_50,
      rhs_product_50,
      lhs_product_49,
      rhs_product_49,
      lhs_product_48,
      rhs_product_48,
      lhs_product_47,
      rhs_product_47,
      lhs_product_46,
      rhs_product_46,
      lhs_product_45,
      rhs_product_45,
      lhs_product_44,
      rhs_product_44,
      lhs_product_43,
      rhs_product_43,
      lhs_product_42,
      rhs_product_42,
      lhs_product_41,
      rhs_product_41,
      lhs_product_40,
      rhs_product_40,
      lhs_product_39,
      rhs_product_39,
      lhs_product_38,
      rhs_product_38,
      lhs_product_37,
      rhs_product_37,
      lhs_product_36,
      rhs_product_36,
      lhs_product_35,
      rhs_product_35,
      lhs_product_34,
      rhs_product_34,
      lhs_product_33,
      rhs_product_33,
      lhs_product_32,
      rhs_product_32,
      lhs_product_31,
      rhs_product_31,
      lhs_product_30,
      rhs_product_30,
      lhs_product_29,
      rhs_product_29,
      lhs_product_28,
      rhs_product_28,
      lhs_product_27,
      rhs_product_27,
      lhs_product_26,
      rhs_product_26,
      lhs_product_25,
      rhs_product_25,
      lhs_product_24,
      rhs_product_24,
      lhs_product_23,
      rhs_product_23,
      lhs_product_22,
      rhs_product_22,
      lhs_product_21,
      rhs_product_21,
      lhs_product_20,
      rhs_product_20,
      lhs_product_19,
      rhs_product_19,
      lhs_product_18,
      rhs_product_18,
      lhs_product_17,
      rhs_product_17,
      lhs_product_16,
      rhs_product_16,
      lhs_product_15,
      rhs_product_15,
      lhs_product_14,
      rhs_product_14,
      lhs_product_13,
      rhs_product_13,
      lhs_product_12,
      rhs_product_12,
      lhs_product_11,
      rhs_product_11,
      lhs_product_10,
      rhs_product_10,
      lhs_product_09,
      rhs_product_09,
      lhs_product_08,
      rhs_product_08,
      lhs_product_07,
      rhs_product_07,
      lhs_product_06,
      rhs_product_06,
      lhs_product_05,
      rhs_product_05,
      lhs_product_04,
      rhs_product_04,
      lhs_product_03,
      rhs_product_03,
      lhs_product_02,
      rhs_product_02,
      lhs_product_01,
      rhs_product_01,
      lhs_product_00, rhs_product_00]
    dsimp only [
      lhs_00,
      lhs_01,
      lhs_02,
      lhs_03,
      lhs_04,
      lhs_05,
      lhs_06,
      lhs_07,
      lhs_08,
      lhs_09,
      lhs_10,
      lhs_11,
      lhs_12,
      lhs_13,
      lhs_14,
      lhs_15,
      lhs_16,
      lhs_17,
      lhs_18,
      lhs_19,
      lhs_20,
      lhs_21,
      lhs_22,
      lhs_23,
      lhs_24,
      lhs_25,
      lhs_26,
      lhs_27,
      lhs_28,
      lhs_29,
      lhs_30,
      lhs_31,
      lhs_32,
      lhs_33,
      lhs_34,
      lhs_35,
      lhs_36,
      lhs_37,
      lhs_38,
      lhs_39,
      lhs_40,
      lhs_41,
      lhs_42,
      lhs_43,
      lhs_44,
      lhs_45,
      lhs_46,
      lhs_47,
      lhs_48,
      lhs_49,
      lhs_50,
      lhs_51,
      lhs_52,
      lhs_53,
      lhs_54,
      lhs_55,
      lhs_56,
      lhs_57,
      lhs_58,
      rhs_00,
      rhs_01,
      rhs_02,
      rhs_03,
      rhs_04,
      rhs_05,
      rhs_06,
      rhs_07,
      rhs_08,
      rhs_09,
      rhs_10,
      rhs_11,
      rhs_12,
      rhs_13,
      rhs_14,
      rhs_15,
      rhs_16,
      rhs_17,
      rhs_18,
      rhs_19,
      rhs_20,
      rhs_21,
      rhs_22,
      rhs_23,
      rhs_24,
      rhs_25,
      rhs_26,
      rhs_27,
      rhs_28,
      rhs_29,
      rhs_30,
      rhs_31,
      rhs_32,
      rhs_33,
      rhs_34,
      rhs_35,
      rhs_36,
      rhs_37,
      rhs_38,
      rhs_39,
      rhs_40,
      rhs_41,
      rhs_42,
      rhs_43,
      rhs_44,
      rhs_45,
      rhs_46,
      rhs_47,
      rhs_48,
      rhs_49,
      rhs_50,
      rhs_51,
      rhs_52,
      rhs_53,
      rhs_54,
      rhs_55,
      rhs_56,
      rhs_57,
      rhs_58]
    ring
  rw [hbalanced] at hproduct_58
  exact lt_irrefl _ hproduct_58

/-- A sweep-realizable coloring cannot contain a Ringel-class
nine-element restriction. -/
theorem IsSweepRealizable.noRingelNineRestrictionOn {n : ℕ}
    {chi : TripleColoring n} (hchi : IsSweepRealizable chi)
    (f : Fin 9 ↪o Fin n) :
    ¬HasRingelNineRestrictionOn chi f :=
  hchi.noRingelNineRestrictionOn_of_nonrealizable
    ringelNine_not_rankThreeVectorRealizable f

/-- A decomposable carrier cannot contain a Ringel-class
nine-element restriction. -/
theorem IsDecomposableOn.noRingelNineRestrictionOn {n : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)}
    (hdecomp : IsDecomposableOn chi s)
    (f : Fin 9 ↪o Fin n) (hf : ∀ i, f i ∈ s) :
    ¬HasRingelNineRestrictionOn chi f :=
  hdecomp.noRingelNineRestrictionOn_of_nonrealizable
    ringelNine_not_rankThreeVectorRealizable f hf

-- END GENERATED RINGEL-NINE CERTIFICATE

end
end ErdosSzekeres

end
