import ErdosSzekeres.Sweep
import Mathlib.Data.Finset.Sort

/-!
# Presenting a finite point set in sweep order

For a finite set of planar points, only finitely many shears make two first
coordinates coincide.  Choosing any other shear and sorting by the resulting
first coordinate produces the normalized `SweptConfiguration` used by the
combinatorial layer.  The shear has determinant one, so it preserves all
orientation values exactly.
-/

namespace ErdosSzekeres

noncomputable section

/-- The first coordinate after applying the determinant-one shear
`(x,y) ↦ (x + t*y,y)`. -/
def sweepCoordinate (t : ℝ) (p : Point 2) : ℝ :=
  p 0 + t * p 1

/-- The determinant-one shear used to make the sweep coordinate generic. -/
def shear (t : ℝ) (p : Point 2) : Point 2 :=
  ![sweepCoordinate t p, p 1]

@[simp] theorem shear_apply_zero (t : ℝ) (p : Point 2) :
    shear t p 0 = sweepCoordinate t p := by
  simp [shear]

@[simp] theorem shear_apply_one (t : ℝ) (p : Point 2) :
    shear t p 1 = p 1 := by
  simp [shear]

/-- Shearing by `t` and then by `-t` returns the original point. -/
@[simp] theorem shear_neg_shear (t : ℝ) (p : Point 2) :
    shear (-t) (shear t p) = p := by
  funext i
  fin_cases i <;> simp [sweepCoordinate]

/-- The determinant-one shear as an invertible linear map. -/
def shearLinearEquiv (t : ℝ) : Point 2 ≃ₗ[ℝ] Point 2 where
  toFun := shear t
  invFun := shear (-t)
  left_inv := shear_neg_shear t
  right_inv p := by simpa using shear_neg_shear (-t) p
  map_add' p q := by
    funext i
    fin_cases i
    · simp [shear, sweepCoordinate]
      ring
    · simp [shear, sweepCoordinate]
  map_smul' u p := by
    funext i
    fin_cases i
    · simp [shear, sweepCoordinate]
      ring
    · simp [shear, sweepCoordinate]

@[simp] theorem shearLinearEquiv_apply (t : ℝ) (p : Point 2) :
    shearLinearEquiv t p = shear t p :=
  rfl

/-- A determinant-one shear preserves the signed orientation value, not just
its sign. -/
@[simp] theorem orientation_shear (t : ℝ) (a b c : Point 2) :
    orientation (shear t a) (shear t b) (shear t c) = orientation a b c := by
  simp only [orientation, shear_apply_zero, shear_apply_one, sweepCoordinate]
  ring

/-- Values of `t` that could arise from equality of two sheared first
coordinates.  Including pairs with equal second coordinate only enlarges this
finite forbidden set and simplifies its definition. -/
def forbiddenSweepParameters (s : Finset (Point 2)) : Finset ℝ :=
  (s ×ˢ s).image fun pq =>
    (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)

theorem exists_parameter_not_forbidden (s : Finset (Point 2)) :
    ∃ t : ℝ, t ∉ forbiddenSweepParameters s := by
  classical
  by_cases h : (forbiddenSweepParameters s).Nonempty
  · let t := (forbiddenSweepParameters s).max' h + 1
    refine ⟨t, ?_⟩
    intro ht
    have hle := (forbiddenSweepParameters s).le_max' t ht
    dsimp [t] at hle
    linarith
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩

/-- A finite set admits a shear whose first coordinate is injective on that
set.  This is the generic-sweep existence lemma. -/
theorem exists_injective_sweepCoordinate (s : Finset (Point 2)) :
    ∃ t : ℝ, Set.InjOn (sweepCoordinate t) s := by
  classical
  obtain ⟨t, ht⟩ := exists_parameter_not_forbidden s
  refine ⟨t, ?_⟩
  intro p hp q hq hpq
  by_contra hne
  have hy : p 1 ≠ q 1 := by
    intro hy
    apply hne
    funext i
    fin_cases i
    · simpa [sweepCoordinate, hy] using hpq
    · exact hy
  have hden : p 1 - q 1 ≠ 0 := sub_ne_zero.mpr hy
  have ht_eq : t = (q 0 - p 0) / (p 1 - q 1) := by
    apply (eq_div_iff hden).2
    dsimp [sweepCoordinate] at hpq
    linarith
  apply ht
  rw [forbiddenSweepParameters, Finset.mem_image]
  exact ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ht_eq.symm⟩

/-- A finite point set together with a determinant-one shear, an enumeration
of its original points, and the resulting normalized swept configuration. -/
structure SweptPresentation (s : Finset (Point 2)) where
  parameter : ℝ
  enumeration : Fin s.card ≃ s
  configuration : SweptConfiguration s.card
  point_eq_shear : ∀ i, configuration.point i = shear parameter (enumeration i : Point 2)

namespace SweptPresentation

variable {s : Finset (Point 2)} (P : SweptPresentation s)

/-- The presentation really enumerates exactly the original finite set. -/
theorem enumeration_mem (i : Fin s.card) : (P.enumeration i : Point 2) ∈ s :=
  (P.enumeration i).property

/-- The orientation of presented points is exactly the orientation of their
original points. -/
theorem orientation_eq (i j k : Fin s.card) :
    orientation (P.configuration.point i) (P.configuration.point j)
        (P.configuration.point k) =
      orientation (P.enumeration i : Point 2) (P.enumeration j : Point 2)
        (P.enumeration k : Point 2) := by
  rw [P.point_eq_shear, P.point_eq_shear, P.point_eq_shear, orientation_shear]

/-- The left/right color in the normalized presentation is the orientation
sign of the corresponding triple in the original point set. -/
theorem tripleColoring_eq_left_iff_original_orientation (t : OrderedTriple s.card) :
    P.configuration.tripleColoring t = Turn.left ↔
      0 < orientation (P.enumeration t.i : Point 2) (P.enumeration t.j : Point 2)
        (P.enumeration t.k : Point 2) := by
  change P.configuration.turn t.i t.j t.k = Turn.left ↔ _
  rw [P.configuration.turn_eq_left_iff, P.orientation_eq]

/-- The right color likewise records a negative original orientation. -/
theorem tripleColoring_eq_right_iff_original_orientation (t : OrderedTriple s.card) :
    P.configuration.tripleColoring t = Turn.right ↔
      orientation (P.enumeration t.i : Point 2) (P.enumeration t.j : Point 2)
        (P.enumeration t.k : Point 2) < 0 := by
  change P.configuration.turn t.i t.j t.k = Turn.right ↔ _
  rw [P.configuration.turn_eq_right_iff t.i t.j t.k t.hij t.hjk, P.orientation_eq]

end SweptPresentation

/-- A copy of the subtype of points in `s`, used internally so that its order
can be supplied solely by the chosen generic sweep coordinate. -/
private structure SweepOrderedPoint (s : Finset (Point 2)) where
  val : s
  deriving Fintype

private def sweepOrderedPointEquiv (s : Finset (Point 2)) :
    SweepOrderedPoint s ≃ s where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

/-- Every finite planar point set in general position has a normalized swept
presentation.  This discharges the coordinate-order assumption at the public
geometry/combinatorics boundary. -/
theorem exists_sweptPresentation (s : Finset (Point 2))
    (hgp : InGeneralPosition s) : Nonempty (SweptPresentation s) := by
  classical
  obtain ⟨t, ht⟩ := exists_injective_sweepCoordinate s
  letI : LinearOrder (SweepOrderedPoint s) :=
      LinearOrder.lift' (fun p : SweepOrderedPoint s => sweepCoordinate t p.val) <| by
    intro ⟨p⟩ ⟨q⟩ hpq
    have hpq' : p = q := Subtype.ext (ht p.property q.property hpq)
    cases hpq'
    rfl
  have hcard : Fintype.card (SweepOrderedPoint s) = s.card := by
    rw [Fintype.card_congr (sweepOrderedPointEquiv s)]
    simp
  let e : Fin s.card ≃o SweepOrderedPoint s :=
    Fintype.orderIsoFinOfCardEq (SweepOrderedPoint s) (k := s.card) hcard
  let enumeration : Fin s.card ≃ s := e.toEquiv.trans (sweepOrderedPointEquiv s)
  let point : Fin s.card → Point 2 := fun i => shear t (enumeration i : Point 2)
  have hmono : StrictMono fun i => point i 0 := by
    intro i j hij
    change sweepCoordinate t (enumeration i : Point 2) <
      sweepCoordinate t (enumeration j : Point 2)
    exact e.lt_iff_lt.mpr hij
  have hgeneral : ∀ ⦃i j k : Fin s.card⦄,
      i ≠ j → i ≠ k → j ≠ k → orientation (point i) (point j) (point k) ≠ 0 := by
    intro i j k hij hik hjk
    rw [show orientation (point i) (point j) (point k) =
      orientation (enumeration i : Point 2) (enumeration j : Point 2)
        (enumeration k : Point 2) by
        simp [point]]
    apply hgp (enumeration i).property (enumeration j).property (enumeration k).property
    · exact fun h => hij (enumeration.injective (Subtype.ext h))
    · exact fun h => hik (enumeration.injective (Subtype.ext h))
    · exact fun h => hjk (enumeration.injective (Subtype.ext h))
  let C : SweptConfiguration s.card :=
    { point := point
      sweep_strictMono := hmono
      generalPosition := hgeneral }
  exact ⟨
    { parameter := t
      enumeration := enumeration
      configuration := C
      point_eq_shear := by intro i; rfl }⟩

end

end ErdosSzekeres
