module

public import ErdosSzekeres.AnchoredPresentation
public import ErdosSzekeres.Extremal

@[expose] public section

/-!
# From the anchored seventeen-point refutation to `ES(6) = 17`

The anchored ES(6) certificate (`ES6Anchored.lean`, kernel-checked LRAT
replay) says that every one-change coloring on seventeen vertices whose
vertex `0` sees every later pair as a right turn contains a strong six-set.
`AnchoredPresentation.lean` proves that anchoring is a normalization of every
swept configuration.  This file composes the two into the planar forcing
statement, the exact formula at six, and the strong-six cardinality ceiling
needed by the predecessor-half recurrence.  It is stated against the
certificate's conclusion as a hypothesis so that it compiles independently
of the multi-hour checkpoint replay; `ES6Certificate.lean` discharges it.
-/

namespace ErdosSzekeres

/-- The conclusion of the anchored seventeen-point certificate. -/
def AnchoredSeventeenForcesStrongSix : Prop :=
  ∀ chi : TripleColoring 17, OneChangeOn chi Finset.univ → chi.IsAnchored →
    ContainsStrongPolygonSet chi Finset.univ 6

/-- Every swept configuration on at least seventeen vertices contains a strong
six-set, given the anchored certificate. -/
theorem SweptConfiguration.containsStrongSix_of_seventeen_le
    (h : AnchoredSeventeenForcesStrongSix) {n : ℕ} (P : SweptConfiguration n)
    (hn : 17 ≤ n) :
    ContainsStrongPolygonSet P.tripleColoring Finset.univ 6 := by
  classical
  let f : Fin 17 ↪o Fin n := Fin.castLEOrderEmb hn
  let P' : SweptConfiguration (16 + 1) := P.restrict f
  let A := Classical.choice P'.exists_anchoredReindexing
  let C := A.configuration
  have hone : OneChangeOn C.tripleColoring Finset.univ :=
    C.tripleColoring_isSweepRealizable.oneChangeOn_univ
  have hC : ContainsStrongPolygonSet C.tripleColoring Finset.univ 6 :=
    h C.tripleColoring hone A.anchored.tripleColoring
  have hP' : ContainsStrongPolygonSet P'.tripleColoring Finset.univ 6 :=
    (A.containsStrongPolygonSet_univ_iff 6).mpr hC
  have hrestrict : P'.tripleColoring = P.tripleColoring.restrict f :=
    P.restrict_tripleColoring f
  rw [hrestrict] at hP'
  have himage :=
    (containsStrongPolygonSet_image_restrict_iff P.tripleColoring f Finset.univ).mp hP'
  exact FinsetPolygon.ContainsStrongPolygonSet.mono himage (Finset.subset_univ _)

/-- Seventeen points in general position contain a convex hexagon, given the
anchored certificate. -/
theorem forces_six_of_anchoredSeventeen (h : AnchoredSeventeenForcesStrongSix) :
    ForcesConvexPolygon 6 17 :=
  forcesConvexPolygon_of_anchored (m := 16) (k := 6) fun C hC =>
    h C.tripleColoring C.tripleColoring_isSweepRealizable.oneChangeOn_univ
      hC.tripleColoring

/-- The strong-six cardinality ceiling at the sweep-coloring interface, given
the anchored certificate. -/
theorem strongSixCeiling_of_anchoredSeventeen (h : AnchoredSeventeenForcesStrongSix)
    {n : ℕ} {χ : TripleColoring n} (hreal : IsSweepRealizable χ)
    (hno : ¬ContainsStrongPolygonSet χ Finset.univ 6) : n ≤ 16 := by
  by_contra hn
  obtain ⟨P, rfl⟩ := hreal
  exact hno (P.containsStrongSix_of_seventeen_le h (by omega))

/-- The classical lower construction gives sixteen points with no convex
hexagon. -/
theorem sharpness_six : HasSharpnessExample 6 17 :=
  classical_lower_sharpness 6 (by omega)

/-- The happy-ending formula is exact at `n = 6`, given the anchored
certificate. -/
theorem erdosSzekeresFormulaAt_six_of_anchoredSeventeen
    (h : AnchoredSeventeenForcesStrongSix) : ErdosSzekeresFormulaAt 6 := by
  norm_num [ErdosSzekeresFormulaAt]
  exact ⟨forces_six_of_anchoredSeventeen h, sharpness_six⟩

end ErdosSzekeres

end
