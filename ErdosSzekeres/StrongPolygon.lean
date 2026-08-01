import ErdosSzekeres.Convexity
import Mathlib.Data.Finset.Sort

/-!
# Strong polygons in the sweep coloring

For four sweep-ordered vertices `i < j < k < l`, convex position is equivalent
to two local color consistencies: the triples `ijk` and `ijl` have the same
color, and the triples `ikl` and `jkl` have the same color.  The four admitted
patterns are a cup, a cap, and the two ways to split the middle vertices
between the upper and lower hull chains.

This file proves that imposing those consistencies on every increasing
four-tuple is exactly geometric convex position for the entire swept point
set.  Thus `IsStrongPolygon` is a purely combinatorial target with a
kernel-checked bridge back to the public convex-hull definition.
-/

namespace ErdosSzekeres

noncomputable section

/-- Equality of turns can be tested by asking whether each turn is left. -/
theorem Turn.eq_iff_left_eq_left (u v : Turn) :
    u = v ↔ (u = Turn.left ↔ v = Turn.left) := by
  cases u <;> cases v <;> simp

/-- The four-index consistency law characterizing a convex polygon in an
ordered triple coloring.  It admits exactly `++++`, `++--`, `--++`, and
`----` on the four increasing triples of each four-tuple. -/
def IsStrongPolygon {n : ℕ} (χ : TripleColoring n) : Prop :=
  ∀ {i j k l : Fin n}, (hij : i < j) → (hjk : j < k) → (hkl : k < l) →
    χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
    χ ⟨i, k, l, hij.trans hjk, hkl⟩ = χ ⟨j, k, l, hjk, hkl⟩

/-- A selected increasing subsequence is a strong polygon when the restricted
coloring satisfies the strong-polygon law. -/
def IsStrongPolygonOn {m n : ℕ} (χ : TripleColoring n) (f : Fin m ↪o Fin n) : Prop :=
  IsStrongPolygon (χ.restrict f)

/-- Every increasing restriction of a strong polygon is a strong polygon. -/
theorem IsStrongPolygon.restrict {m n : ℕ} {χ : TripleColoring n}
    (hχ : IsStrongPolygon χ) (f : Fin m ↪o Fin n) :
    IsStrongPolygonOn χ f := by
  intro i j k l hij hjk hkl
  exact hχ (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)

/-- Transfer a selected strong polygon back through an ambient coloring
restriction whose coloring is known exactly. -/
theorem IsStrongPolygonOn.of_trans_of_restrict_eq {n m k : ℕ}
    {χ : TripleColoring n} {ψ : TripleColoring m}
    (e : Fin m ↪o Fin n) (hrestrict : χ.restrict e = ψ)
    (f : Fin k ↪o Fin m) (h : IsStrongPolygonOn χ (f.trans e)) :
    IsStrongPolygonOn ψ f := by
  subst ψ
  have hcolor : (χ.restrict e).restrict f = χ.restrict (f.trans e) := by
    funext t
    cases t
    rfl
  rw [IsStrongPolygonOn, hcolor]
  exact h

/-- General position is inherited by finite subsets. -/
theorem InGeneralPosition.mono {s t : Finset (Point 2)}
    (hs : InGeneralPosition s) (hts : t ⊆ s) : InGeneralPosition t := by
  intro a ha b hb c hc
  exact hs (hts ha) (hts hb) (hts hc)

namespace SweptConfiguration

variable {n : ℕ} (P : SweptConfiguration n)

/-- The finite set of points underlying a swept configuration. -/
def pointFinset : Finset (Point 2) :=
  Finset.univ.image P.point

@[simp] theorem mem_pointFinset (i : Fin n) : P.point i ∈ P.pointFinset := by
  simp [pointFinset]

@[simp] theorem card_pointFinset : P.pointFinset.card = n := by
  rw [pointFinset, Finset.card_image_of_injective _ P.point_injective]
  simp

/-- The underlying point set of a swept configuration is in general
position. -/
theorem pointFinset_generalPosition : InGeneralPosition P.pointFinset := by
  intro a ha b hb c hc hab hac hbc
  simp only [pointFinset, Finset.mem_image, Finset.mem_univ, true_and] at ha hb hc
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, rfl⟩ := hc
  apply P.generalPosition
  · exact fun hij => hab (congrArg P.point hij)
  · exact fun hik => hac (congrArg P.point hik)
  · exact fun hjk => hbc (congrArg P.point hjk)

private theorem orientation_middle_left_signs (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : orientation a b c < 0) (habd : 0 < orientation a b d) :
    0 < orientation a c d ∧ 0 < orientation b c d := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem orientation_middle_left_signs' (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : 0 < orientation a b c) (habd : orientation a b d < 0) :
    orientation a c d < 0 ∧ orientation b c d < 0 := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem orientation_middle_right_signs (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (hacd : orientation a c d < 0) (hbcd : 0 < orientation b c d) :
    orientation a b c < 0 ∧ orientation a b d < 0 := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem orientation_middle_right_signs' (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (hacd : 0 < orientation a c d) (hbcd : orientation b c d < 0) :
    0 < orientation a b c ∧ 0 < orientation a b d := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem left_endpoint_not_inside (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    ¬ InsideTriangleBySigns b c d a := by
  rintro (⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩) <;>
    simp only [orientation] at * <;> nlinarith

private theorem right_endpoint_not_inside (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    ¬ InsideTriangleBySigns a b c d := by
  rintro (⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩) <;>
    simp only [orientation] at * <;> nlinarith

private theorem middle_left_inside_iff (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    InsideTriangleBySigns a c d b ↔
      ((orientation a b c < 0 ∧ 0 < orientation a b d) ∨
       (0 < orientation a b c ∧ orientation a b d < 0)) := by
  constructor
  · rintro (⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩)
    · left
      simp only [orientation] at *
      constructor <;> nlinarith
    · right
      simp only [orientation] at *
      constructor <;> nlinarith
  · rintro (⟨habc, habd⟩ | ⟨habc, habd⟩)
    · left
      obtain ⟨hacd, hbcd⟩ :=
        orientation_middle_left_signs a b c d hab hbc hcd habc habd
      refine ⟨hacd, ?_, ?_, ?_⟩ <;>
        simp only [orientation] at * <;> nlinarith
    · right
      obtain ⟨hacd, hbcd⟩ :=
        orientation_middle_left_signs' a b c d hab hbc hcd habc habd
      refine ⟨hacd, ?_, ?_, ?_⟩ <;>
        simp only [orientation] at * <;> nlinarith

private theorem middle_right_inside_iff (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0) :
    InsideTriangleBySigns a b d c ↔
      ((orientation a c d < 0 ∧ 0 < orientation b c d) ∨
       (0 < orientation a c d ∧ orientation b c d < 0)) := by
  constructor
  · rintro (⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩)
    · right
      simp only [orientation] at *
      constructor <;> nlinarith
    · left
      simp only [orientation] at *
      constructor <;> nlinarith
  · rintro (⟨hacd, hbcd⟩ | ⟨hacd, hbcd⟩)
    · right
      obtain ⟨habc, habd⟩ :=
        orientation_middle_right_signs a b c d hab hbc hcd hacd hbcd
      refine ⟨habd, habc, ?_, ?_⟩ <;>
        simp only [orientation] at * <;> nlinarith
    · left
      obtain ⟨habc, habd⟩ :=
        orientation_middle_right_signs' a b c d hab hbc hcd hacd hbcd
      refine ⟨habd, habc, ?_, ?_⟩ <;>
        simp only [orientation] at * <;> nlinarith

private theorem not_opposite_sign_iff (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ¬ ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ↔ (0 < x ↔ 0 < y) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos <;>
    rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have hnx : ¬ 0 < x := not_lt_of_ge hxneg.le
    have hny : ¬ 0 < y := not_lt_of_ge hyneg.le
    simp [hxneg, hyneg, hnx, hny]
  · have hnx : ¬ 0 < x := not_lt_of_ge hxneg.le
    simp [hxneg, hypos, hnx]
  · have hny : ¬ 0 < y := not_lt_of_ge hyneg.le
    simp [hxpos, hyneg, hny]
  · simp [hxpos, hypos, hxpos.le, hypos.le]

/-- For four points with increasing sweep coordinate, geometric convexity is
equivalent to the two orientation-sign consistencies defining a strong
polygon. -/
theorem inConvexPosition_four_iff_orientation_consistency_of_x_order
    (a b c d : Point 2)
    (habx : a 0 < b 0) (hbcx : b 0 < c 0) (hcdx : c 0 < d 0)
    (hgp : InGeneralPosition {a, b, c, d}) :
    InConvexPosition {a, b, c, d} ↔
      ((0 < orientation a b c ↔ 0 < orientation a b d) ∧
       (0 < orientation a c d ↔ 0 < orientation b c d)) := by
  have hab : a ≠ b := by
    intro h
    subst b
    linarith
  have hac : a ≠ c := by
    intro h
    subst c
    linarith
  have had : a ≠ d := by
    intro h
    subst d
    linarith
  have hbc : b ≠ c := by
    intro h
    subst c
    linarith
  have hbd : b ≠ d := by
    intro h
    subst d
    linarith
  have hcd : c ≠ d := by
    intro h
    subst d
    linarith
  rw [inConvexPosition_four_iff_orientation_signs a b c d hgp
    hab hac had hbc hbd hcd]
  rw [middle_left_inside_iff a b c d habx hbcx hcdx,
    middle_right_inside_iff a b c d habx hbcx hcdx]
  have hleft := left_endpoint_not_inside a b c d habx hbcx hcdx
  have hright := right_endpoint_not_inside a b c d habx hbcx hcdx
  simp only [hleft, hright, not_false_eq_true, true_and, and_true]
  have habc : orientation a b c ≠ 0 :=
    hgp (by simp) (by simp) (by simp) hab hac hbc
  have habd : orientation a b d ≠ 0 :=
    hgp (by simp) (by simp) (by simp) hab had hbd
  have hacd : orientation a c d ≠ 0 :=
    hgp (by simp) (by simp) (by simp) hac had hcd
  have hbcd : orientation b c d ≠ 0 :=
    hgp (by simp) (by simp) (by simp) hbc hbd hcd
  rw [not_opposite_sign_iff _ _ habc habd,
    not_opposite_sign_iff _ _ hacd hbcd]

/-- The local geometric meaning of the strong-polygon law for four increasing
indices of a swept configuration. -/
theorem inConvexPosition_four_iff_turn_consistency
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    InConvexPosition {P.point i, P.point j, P.point k, P.point l} ↔
      (P.turn i j k = P.turn i j l ∧ P.turn i k l = P.turn j k l) := by
  have hgp : InGeneralPosition {P.point i, P.point j, P.point k, P.point l} :=
    P.pointFinset_generalPosition.mono (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact P.mem_pointFinset _)
  simpa only [Turn.eq_iff_left_eq_left, P.turn_eq_left_iff] using
    inConvexPosition_four_iff_orientation_consistency_of_x_order
      (P.point i) (P.point j) (P.point k) (P.point l)
      (P.sweep_strictMono hij) (P.sweep_strictMono hjk)
      (P.sweep_strictMono hkl) hgp

/-- The full combinatorial/geometric bridge: a swept finite point set is in
convex position exactly when its ordered triple coloring is a strong polygon. -/
theorem inConvexPosition_pointFinset_iff_isStrongPolygon :
    InConvexPosition P.pointFinset ↔ IsStrongPolygon P.tripleColoring := by
  classical
  constructor
  · intro hconv i j k l hij hjk hkl
    apply (P.inConvexPosition_four_iff_turn_consistency i j k l hij hjk hkl).mp
    exact hconv.mono (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact P.mem_pointFinset _)
  · intro hstrong
    apply (inConvexPosition_iff_four_subsets P.pointFinset
      P.pointFinset_generalPosition).2
    intro t hts htcard
    have hts' : t ⊆ Finset.univ.image P.point := by
      simpa [pointFinset] using hts
    obtain ⟨u, hu⟩ := Finset.subset_univ_image_iff.mp hts'
    have hucard : u.card = 4 := by
      calc
        u.card = (u.image P.point).card :=
          (Finset.card_image_of_injective u P.point_injective).symm
        _ = t.card := congrArg Finset.card hu
        _ = 4 := htcard
    let f : Fin 4 ↪o Fin n := u.orderEmbOfFin hucard
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have h23 : f 2 < f 3 := f.strictMono (by decide)
    have hlocal : InConvexPosition
        {P.point (f 0), P.point (f 1), P.point (f 2), P.point (f 3)} :=
      (P.inConvexPosition_four_iff_turn_consistency
        (f 0) (f 1) (f 2) (f 3) h01 h12 h23).2
        (hstrong h01 h12 h23)
    have hfin4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    have hfu : ({f 0, f 1, f 2, f 3} : Finset (Fin n)) = u := by
      calc
        ({f 0, f 1, f 2, f 3} : Finset (Fin n)) = Finset.univ.image f := by
          rw [hfin4]
          simp
        _ = u := by
          simp [f]
    rw [← hu, ← hfu]
    simpa only [Finset.image_insert, Finset.image_singleton] using hlocal

end SweptConfiguration

namespace SweptPresentation

variable {s : Finset (Point 2)} (P : SweptPresentation s)

/-- The original enumeration of a presentation has image exactly `s`. -/
theorem enumeration_pointFinset :
    Finset.univ.image (fun i => (P.enumeration i : Point 2)) = s := by
  ext p
  constructor
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, rfl⟩
    exact (P.enumeration i).property
  · intro hp
    obtain ⟨i, hi⟩ := P.enumeration.surjective ⟨p, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact congrArg Subtype.val hi

/-- The swept configuration's point set is exactly the determinant-one shear
of the original public point set. -/
theorem configuration_pointFinset_eq_image_shear :
    P.configuration.pointFinset = s.image (shearLinearEquiv P.parameter) := by
  rw [SweptConfiguration.pointFinset]
  calc
    Finset.univ.image P.configuration.point =
        Finset.univ.image
          (fun i => shearLinearEquiv P.parameter (P.enumeration i : Point 2)) := by
      apply Finset.image_congr
      intro i _
      simpa using P.point_eq_shear i
    _ = (Finset.univ.image (fun i => (P.enumeration i : Point 2))).image
          (shearLinearEquiv P.parameter) := by
      rw [Finset.image_image]
      rfl
    _ = s.image (shearLinearEquiv P.parameter) := by rw [P.enumeration_pointFinset]

/-- The public version of the strong-polygon bridge.  For any swept
presentation, the original finite point set is in convex position exactly
when the presentation's triple coloring satisfies the four-index law. -/
theorem inConvexPosition_iff_isStrongPolygon :
    InConvexPosition s ↔ IsStrongPolygon P.configuration.tripleColoring := by
  calc
    InConvexPosition s ↔
        InConvexPosition (s.image (shearLinearEquiv P.parameter)) :=
      (inConvexPosition_image_linearEquiv_iff
        (shearLinearEquiv P.parameter) s).symm
    _ ↔ InConvexPosition P.configuration.pointFinset := by
      rw [P.configuration_pointFinset_eq_image_shear]
    _ ↔ IsStrongPolygon P.configuration.tripleColoring :=
      P.configuration.inConvexPosition_pointFinset_iff_isStrongPolygon

/-- The original points selected by an increasing embedding of presentation
indices. -/
def selectedPointFinset {k : ℕ} (f : Fin k ↪o Fin s.card) :
    Finset (Point 2) :=
  Finset.univ.image fun i => (P.enumeration (f i) : Point 2)

theorem selectedPointFinset_subset {k : ℕ} (f : Fin k ↪o Fin s.card) :
    P.selectedPointFinset f ⊆ s := by
  intro p hp
  simp only [selectedPointFinset, Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨i, rfl⟩ := hp
  exact P.enumeration_mem (f i)

@[simp] theorem card_selectedPointFinset {k : ℕ} (f : Fin k ↪o Fin s.card) :
    (P.selectedPointFinset f).card = k := by
  have hinjective : Function.Injective
      (fun i => (P.enumeration (f i) : Point 2)) := by
    intro i j hij
    apply f.injective
    apply P.enumeration.injective
    exact Subtype.ext hij
  rw [selectedPointFinset, Finset.card_image_of_injective _ hinjective]
  simp

/-- The restricted swept configuration is the shear of exactly the selected
original points. -/
theorem restrict_pointFinset_eq_image_selectedPointFinset {k : ℕ}
    (f : Fin k ↪o Fin s.card) :
    (P.configuration.restrict f).pointFinset =
      (P.selectedPointFinset f).image (shearLinearEquiv P.parameter) := by
  rw [SweptConfiguration.pointFinset, selectedPointFinset]
  calc
    Finset.univ.image (P.configuration.restrict f).point =
        Finset.univ.image
          (fun i => shearLinearEquiv P.parameter
            (P.enumeration (f i) : Point 2)) := by
      apply Finset.image_congr
      intro i _
      simpa using P.point_eq_shear (f i)
    _ = (Finset.univ.image
          (fun i => (P.enumeration (f i) : Point 2))).image
            (shearLinearEquiv P.parameter) := by
      rw [Finset.image_image]
      rfl

/-- A selected subset of the original points is geometrically convex exactly
when its increasingly restricted coloring is a strong polygon. -/
theorem inConvexPosition_selectedPointFinset_iff_isStrongPolygonOn {k : ℕ}
    (f : Fin k ↪o Fin s.card) :
    InConvexPosition (P.selectedPointFinset f) ↔
      IsStrongPolygonOn P.configuration.tripleColoring f := by
  calc
    InConvexPosition (P.selectedPointFinset f) ↔
        InConvexPosition ((P.selectedPointFinset f).image
          (shearLinearEquiv P.parameter)) :=
      (inConvexPosition_image_linearEquiv_iff
        (shearLinearEquiv P.parameter) (P.selectedPointFinset f)).symm
    _ ↔ InConvexPosition (P.configuration.restrict f).pointFinset := by
      rw [P.restrict_pointFinset_eq_image_selectedPointFinset f]
    _ ↔ IsStrongPolygon (P.configuration.restrict f).tripleColoring :=
      (P.configuration.restrict f).inConvexPosition_pointFinset_iff_isStrongPolygon
    _ ↔ IsStrongPolygonOn P.configuration.tripleColoring f := by
      rw [P.configuration.restrict_tripleColoring f]
      rfl

/-- The public convex-subset predicate is exactly existence of an increasing
restriction whose coloring is a strong polygon. -/
theorem containsConvexSubset_iff_exists_isStrongPolygonOn (k : ℕ) :
    ContainsConvexSubset s k ↔
      ∃ f : Fin k ↪o Fin s.card,
        IsStrongPolygonOn P.configuration.tripleColoring f := by
  classical
  constructor
  · rintro ⟨t, hts, htcard, htconvex⟩
    have hts' : t ⊆ Finset.univ.image
        (fun i => (P.enumeration i : Point 2)) := by
      simpa [P.enumeration_pointFinset] using hts
    obtain ⟨u, hu⟩ := Finset.subset_univ_image_iff.mp hts'
    have hucard : u.card = k := by
      have hinjective : Function.Injective
          (fun i => (P.enumeration i : Point 2)) := by
        intro i j hij
        apply P.enumeration.injective
        exact Subtype.ext hij
      calc
        u.card = (u.image (fun i => (P.enumeration i : Point 2))).card :=
          (Finset.card_image_of_injective u hinjective).symm
        _ = t.card := congrArg Finset.card hu
        _ = k := htcard
    let f : Fin k ↪o Fin s.card := u.orderEmbOfFin hucard
    have hselected : P.selectedPointFinset f = t := by
      calc
        P.selectedPointFinset f =
            (Finset.univ.image f).image
              (fun i => (P.enumeration i : Point 2)) := by
          rw [selectedPointFinset, Finset.image_image]
          rfl
        _ = u.image (fun i => (P.enumeration i : Point 2)) := by
          rw [Finset.image_orderEmbOfFin_univ]
        _ = t := hu
    refine ⟨f, (P.inConvexPosition_selectedPointFinset_iff_isStrongPolygonOn f).mp ?_⟩
    rwa [hselected]
  · rintro ⟨f, hstrong⟩
    exact ⟨P.selectedPointFinset f, P.selectedPointFinset_subset f,
      P.card_selectedPointFinset f,
      (P.inConvexPosition_selectedPointFinset_iff_isStrongPolygonOn f).mpr hstrong⟩

end SweptPresentation

/-- Every finite planar set in general position admits a presentation whose
strong-polygon predicate is equivalent to convex position.  This packages the
existence of a generic sweep with the public bridge above. -/
theorem inConvexPosition_iff_exists_strongPolygonPresentation
    (s : Finset (Point 2)) (hgp : InGeneralPosition s) :
    InConvexPosition s ↔
      ∃ P : SweptPresentation s,
        IsStrongPolygon P.configuration.tripleColoring := by
  constructor
  · intro hconv
    let P := Classical.choice (exists_sweptPresentation s hgp)
    exact ⟨P, P.inConvexPosition_iff_isStrongPolygon.mp hconv⟩
  · rintro ⟨P, hstrong⟩
    exact P.inConvexPosition_iff_isStrongPolygon.mpr hstrong

end

end ErdosSzekeres
