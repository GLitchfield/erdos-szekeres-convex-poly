module

public import ErdosSzekeres.StructuralChargingPascalTails
public import ErdosSzekeres.StructuralChargingNextState578

@[expose] public section

/-!
# State 578 as an instance of the uniform Pascal-tail reduction

The two state-specific residual reservoirs, 32 and 41, are exactly the two
uniform Pascal-tail reservoirs.  This file records the bridge so later work
can use the all-parameter reducer without losing the established state-578
gate interfaces.
-/

namespace ErdosSzekeres

theorem lowerPascalTailReservoir_578 :
    lowerPascalTailReservoir 5 7 8 = 32 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem upperPascalTailReservoir_578 :
    upperPascalTailReservoir 5 7 8 = 41 := by
  norm_num [upperPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem singletonLowerPascalTailGate_578_iff :
    SingletonLowerPascalTailGate 5 7 8 ↔ SingletonLowerCriticalGate578 := by
  rw [SingletonLowerPascalTailGate, SingletonLowerCriticalGate578,
    lowerPascalTailReservoir_578]

theorem singletonUpperPascalTailGate_578_iff :
    SingletonUpperPascalTailGate 5 7 8 ↔ SingletonUpperCriticalGate578 := by
  rw [SingletonUpperPascalTailGate, SingletonUpperCriticalGate578,
    upperPascalTailReservoir_578]

/-- The former state-specific tail dispatcher is an exact instance of the
uniform Pascal-tail theorem. -/
theorem criticalRootImpossible_578_of_predecessors_uniform_pascal_tail_gates
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8)
    (hlowerGate : SingletonLowerCriticalGate578)
    (hupperGate : SingletonUpperCriticalGate578) :
    DecomposableCriticalRootImpossible 5 7 8 := by
  exact criticalRootImpossible_of_predecessors_pascal_tail_gates
    (a := 5) (u := 7) (k := 8)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hpredecessors (singletonLowerPascalTailGate_578_iff.mpr hlowerGate)
    (singletonUpperPascalTailGate_578_iff.mpr hupperGate)

end ErdosSzekeres

end
