import ErdosSzekeres.ES5CNFGenerated

/-!
# Kernel-checked finite certificate for the nine-point case

The CNF variables are the 84 increasing triples on nine ordered vertices.
The clauses impose the rank-three one-change axiom on every four vertices and
forbid every strong coloring on every five-subset. The accompanying LRAT trace
certifies that these requirements are inconsistent.
-/

namespace ErdosSzekeres

theorem SweptConfiguration.exists_strong_five (P : SweptConfiguration 9) :
    ∃ f : Fin 5 ↪o Fin 9, IsStrongPolygonOn P.tripleColoring f := by
  by_contra h
  push Not at h
  have hcnf : ES5CNF P.tripleColoring :=
    es5CNF_of_signotope_noStrong P.tripleColoring
      (fun a b c d hab hbc hcd =>
        P.turnSequenceAllowed a b c d hab hbc hcd)
      h
  exact es5CNF_unsat P.tripleColoring hcnf

/-- Every swept configuration with at least nine vertices contains a strong
five-vertex increasing restriction. -/
theorem SweptConfiguration.exists_strong_five_of_nine_le
    {n : ℕ} (P : SweptConfiguration n) (hn : 9 ≤ n) :
    ∃ f : Fin 5 ↪o Fin n, IsStrongPolygonOn P.tripleColoring f := by
  let e : Fin 9 ↪o Fin n := Finset.univ.orderEmbOfCardLe (by simpa using hn)
  obtain ⟨f, hf⟩ := (P.restrict e).exists_strong_five
  let g : Fin 5 ↪o Fin n := f.trans e
  refine ⟨g, ?_⟩
  intro i j k l hij hjk hkl
  exact hf hij hjk hkl

/-- The kernel-checked nine-point upper bound for the happy-ending problem at
five vertices. -/
theorem forces_five : ForcesConvexPolygon 5 9 := by
  intro s hcard hgp
  let P := Classical.choice (exists_sweptPresentation s hgp)
  obtain ⟨f, hf⟩ := P.configuration.exists_strong_five_of_nine_le hcard
  exact (P.containsConvexSubset_iff_exists_isStrongPolygonOn 5).2 ⟨f, hf⟩

/-- The classical lower construction gives eight points with no convex
pentagon. -/
theorem sharpness_five : HasSharpnessExample 5 9 := by
  exact classical_lower_sharpness 5 (by omega)

/-- The happy-ending formula is exact at `n = 5`: nine points force a convex
pentagon, while eight points need not contain one. -/
theorem erdosSzekeresFormulaAt_five : ErdosSzekeresFormulaAt 5 := by
  norm_num [ErdosSzekeresFormulaAt]
  exact ⟨forces_five, sharpness_five⟩

end ErdosSzekeres
