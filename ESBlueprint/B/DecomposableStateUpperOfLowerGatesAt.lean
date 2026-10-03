import ErdosSzekeres.StructuralChargingPascalTailGates
import ErdosSzekeres.DecomposableContextLemmas
import ErdosSzekeres.RingelNineNonrealizable

namespace ErdosSzekeres

/-- Classical regime: Erdős–Szekeres on the restriction to a decomposable carrier. -/
private theorem decomposableStateUpper_of_classic_aux {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u)
    (hbase : a + u ≤ k + 3) : DecomposableStateUpper a u k := by
  intro n χ s hdec hlt
  rw [decomposableThreshold_eq_choose ha hu hbase] at hlt
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have hsweep : IsSweepRealizable (χ.restrict e) :=
    hdec.restrict_isSweepRealizable e (fun i => s.orderEmbOfFin_mem rfl i)
  have hcard : Nat.choose (a + u - 4) (a - 2) <
      (Finset.univ : Finset (Fin s.card)).card := by
    simpa using hlt
  have himage : (Finset.univ : Finset (Fin s.card)).image e = s :=
    s.image_orderEmbOfFin_univ rfl
  rcases containsCapSet_or_containsCupSet_of_choose_lt hsweep Finset.univ ha hu hcard with
    hcap | hcup
  · left
    have h := containsCapSet_map_restrict e hcap
    rwa [himage] at h
  · right; left
    have h := containsCupSet_map_restrict e hcup
    rwa [himage] at h

/-- Gate assembly for Theorem 8 at a fixed strong-polygon parameter k: if the singleton lower Pascal-tail gate holds at every active state (a,u,k) with a < k, then every decomposable state (a,u,k) is bounded by the Baek-Balko threshold. Strong induction on a+u: the classic regime by Erdős-Szekeres on the decomposable carrier, parameters above k by threshold monotonicity, and active states through the interior Pascal-tail shell with colour-dual upper gates.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.criticalRootImpossible_of_predecessors_interior_pascal_tail_gates, ErdosSzekeres.singletonUpperPascalTailGate_iff_lower_dual, ErdosSzekeres.containsCapSet_or_containsCupSet_of_choose_lt
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem decomposableStateUpper_of_lower_gates_at {k : ℕ} (hk : 2 ≤ k) (hgate : ∀ a u, 4 ≤ a → 4 ≤ u → a < k → u ≤ k → k + 4 ≤ a + u → SingletonLowerPascalTailGate a u k) : ∀ a u, DecomposableStateUpper a u k := by
  suffices h : ∀ m a u, a + u = m → DecomposableStateUpper a u k by
    intro a u
    exact h _ a u rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a u hm
  subst hm
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · intro n χ s hdec _
    interval_cases a
    · exact Or.inl ⟨∅, Finset.empty_subset _, rfl, fun t hi => by simp at hi⟩
    · exact Or.inl (containsCapSet_one hdec.nonempty)
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · intro n χ s hdec _
    interval_cases u
    · exact Or.inr (Or.inl ⟨∅, Finset.empty_subset _, rfl, fun t hi => by simp at hi⟩)
    · exact Or.inr (Or.inl (containsCupSet_one hdec.nonempty))
  rcases Nat.lt_or_ge k a with hka | hka
  · intro n χ s hdec hlt
    have hmono : decomposableThreshold k u k ≤ decomposableThreshold a u k :=
      decomposableThreshold_mono hk hu2 hka.le le_rfl
    rcases ih (k + u) (by omega) k u rfl hdec (lt_of_le_of_lt hmono hlt) with
      hcap | hcup | hstrong
    · exact Or.inr (Or.inr (FinsetPolygon.ContainsCapSet.toContainsStrongPolygonSet hcap))
    · exact Or.inr (Or.inl hcup)
    · exact Or.inr (Or.inr hstrong)
  rcases Nat.lt_or_ge k u with hku | hku
  · intro n χ s hdec hlt
    have hmono : decomposableThreshold a k k ≤ decomposableThreshold a u k :=
      decomposableThreshold_mono ha2 hk le_rfl hku.le
    rcases ih (a + k) (by omega) a k rfl hdec (lt_of_le_of_lt hmono hlt) with
      hcap | hcup | hstrong
    · exact Or.inl hcap
    · exact Or.inr (Or.inr (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet hcup))
    · exact Or.inr (Or.inr hstrong)
  have hak : a ≤ k := hka
  have huk : u ≤ k := hku
  rcases Nat.lt_or_ge (k + 3) (a + u) with hbase | hbase
  swap
  · exact @decomposableStateUpper_of_classic_aux a u k ha2 hu2 hbase
  have hactive : k + 4 ≤ a + u := by omega
  have ha4 : 4 ≤ a := by omega
  have hu4 : 4 ≤ u := by omega
  apply rootTransitionUpper_implies_decomposableStateUpper (one_le_decomposableThreshold ha2 hu2)
  apply criticalRootImpossible_implies_rootTransitionUpper
  apply criticalRootImpossible_of_predecessors_interior_pascal_tail_gates ha4 hu4 hak huk hactive
  · intro a' u' hlt'
    exact ih (a' + u') hlt' a' u' rfl
  · intro haLt
    exact lowerPascalTailCriticalGate_of_singleton ha4 hu4 hak hactive
      (hgate a u ha4 hu4 haLt huk hactive)
  · intro huLt
    exact upperPascalTailCriticalGate_of_singleton ha4 hu4 hak huk hactive
      ((singletonUpperPascalTailGate_iff_lower_dual ha2 hu2 hak huk).mpr
        (hgate u a hu4 ha4 huLt hak (by omega)))

end ErdosSzekeres
