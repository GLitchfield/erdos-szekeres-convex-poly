import ErdosSzekeres.DecompositionPrimeMutationCreationShield
import ESBlueprint.B.DeepSplitStrongAvoidanceIff
import ESBlueprint.B.DeepSplitEndpointConstraintsIff

namespace ErdosSzekeres

/-- Independent decomposable child colorings on disjoint fixed ordered supports glue at exact cardinal sum when their pure and opposite-endpoint cup/cap predicates and every lower-cup/upper-cap strong coupling hold. The parent agrees on every child triple, is decomposable and obeys all chain predicates and strong avoidance.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.deepSplit_strong_avoidance_iff, ErdosSzekeres.deepSplit_endpoint_constraints_iff, ErdosSzekeres.IsDecomposableOn.of_agreeOnTriples, ErdosSzekeres.isStrongPolygonSet_congr_of_agreeOnTriples
@dangling-ok General sufficiency component of R24 exact DS compatible-profile max-plus law; fixed joint supports and independent child colors are allowed, while abstract joint placement, occupancy maxima and closed loss invariant remain separate obligations. -/
theorem deepSplit_profile_gluing_exists {n s : ℕ} (ψL ψU : TripleColoring n) {lower upper : Finset (Fin n)} (hdis : Disjoint lower upper) (hLdec : IsDecomposableOn ψL lower) (hUdec : IsDecomposableOn ψU upper) (hnoL : ¬ ContainsStrongPolygonSet ψL lower (s + 1)) (hnoU : ¬ ContainsStrongPolygonSet ψU upper (s + 1)) (cupAllowed capAllowed : Finset (Fin n) → Prop) (hCupU : ∀ T : Finset (Fin n), T ⊆ upper → IsCupSet ψU T → cupAllowed T) (hCapL : ∀ T : Finset (Fin n), T ⊆ lower → IsCapSet ψL T → capAllowed T) (hCupMixed : ∀ C E : Finset (Fin n), C ⊆ lower → E ⊆ upper → IsCupSet ψL C → (∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) → cupAllowed (C ∪ E)) (hCapMixed : ∀ C E : Finset (Fin n), C ⊆ upper → E ⊆ lower → IsCapSet ψU C → (∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) → capAllowed (C ∪ E)) (hcouple : ∀ C D : Finset (Fin n), C ⊆ lower → D ⊆ upper → IsCupSet ψL C → IsCapSet ψU D → C.card + D.card ≤ s) : ∃ χ : TripleColoring n, χ.AgreeOnTriples ψL lower ∧ χ.AgreeOnTriples ψU upper ∧ HasDeepBelowSplit χ lower upper ∧ IsDecomposableOn χ (lower ∪ upper) ∧ (¬ ContainsStrongPolygonSet χ (lower ∪ upper) (s + 1)) ∧ (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCupSet χ T → cupAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCapSet χ T → capAllowed T) ∧ (lower ∪ upper).card = lower.card + upper.card := by
  classical
  let χ : TripleColoring n := fun t =>
    if t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower then ψL t
    else if t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper then ψU t
    else if t.j ∈ lower then Turn.left else Turn.right
  have hagreeL : χ.AgreeOnTriples ψL lower := by
    intro t hi hj hk
    simp [χ, hi, hj, hk]
  have hagreeU : χ.AgreeOnTriples ψU upper := by
    intro t hi hj hk
    have hnL : ¬ (t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      intro h
      exact Finset.disjoint_left.mp hdis h.2.1 hj
    simp [χ, hnL, hi, hj, hk]
  have hdeep : HasDeepBelowSplit χ lower upper := by
    refine ⟨hdis, ?_⟩
    intro t hi hj hk hnL hnU
    simp [χ, hnL, hnU]
  have cup_transfer (ψ : TripleColoring n) (S T : Finset (Fin n))
      (hTS : T ⊆ S) (hagree : χ.AgreeOnTriples ψ S)
      (hT : IsCupSet χ T) : IsCupSet ψ T := by
    intro t hi hj hk
    exact (hagree t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
  have cap_transfer (ψ : TripleColoring n) (S T : Finset (Fin n))
      (hTS : T ⊆ S) (hagree : χ.AgreeOnTriples ψ S)
      (hT : IsCapSet χ T) : IsCapSet ψ T := by
    intro t hi hj hk
    exact (hagree t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
  have no_strong_transfer (ψ : TripleColoring n) (S : Finset (Fin n))
      (hagree : χ.AgreeOnTriples ψ S)
      (hno : ¬ ContainsStrongPolygonSet ψ S (s + 1)) :
      ¬ ContainsStrongPolygonSet χ S (s + 1) := by
    rintro ⟨T, hTS, hTcard, hT⟩
    apply hno
    refine ⟨T, hTS, hTcard, ?_⟩
    exact (isStrongPolygonSet_congr_of_agreeOnTriples
      (fun t hi hj hk ↦ hagree t (hTS hi) (hTS hj) (hTS hk))).mp hT
  have hLdec' : IsDecomposableOn χ lower :=
    hLdec.of_agreeOnTriples (fun t hi hj hk ↦ (hagreeL t hi hj hk).symm)
  have hUdec' : IsDecomposableOn χ upper :=
    hUdec.of_agreeOnTriples (fun t hi hj hk ↦ (hagreeU t hi hj hk).symm)
  have hno : ¬ ContainsStrongPolygonSet χ (lower ∪ upper) (s + 1) := by
    apply (deepSplit_strong_avoidance_iff hdeep).mpr
    refine ⟨no_strong_transfer ψL lower hagreeL hnoL,
      no_strong_transfer ψU upper hagreeU hnoU, ?_⟩
    intro C D hCL hDU hC hD
    exact hcouple C D hCL hDU
      (cup_transfer ψL lower C hCL hagreeL hC)
      (cap_transfer ψU upper D hDU hagreeU hD)
  have hconstraints :
      (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCupSet χ T → cupAllowed T) ∧
      (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCapSet χ T → capAllowed T) := by
    apply (deepSplit_endpoint_constraints_iff hdeep cupAllowed capAllowed).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T hTU hT
      exact hCupU T hTU (cup_transfer ψU upper T hTU hagreeU hT)
    · intro T hTL hT
      exact hCapL T hTL (cap_transfer ψL lower T hTL hagreeL hT)
    · intro C E hCL hEU hC hend
      exact hCupMixed C E hCL hEU
        (cup_transfer ψL lower C hCL hagreeL hC) hend
    · intro C E hCU hEL hC hend
      exact hCapMixed C E hCU hEL
        (cap_transfer ψU upper C hCU hagreeU hC) hend
  exact ⟨χ, hagreeL, hagreeU, hdeep, .split hLdec' hUdec' hdeep,
    hno, hconstraints.1, hconstraints.2, Finset.card_union_of_disjoint hdis⟩


end ErdosSzekeres
