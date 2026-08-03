module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate for the eight-vertex `(4,5,5)` state. -/

namespace ErdosSzekeres

lrat_proof e3State455_cnf_unsat
  (include_str "../certificates/e3-signotope-8-4-5-5.cnf")
  (include_str "../certificates/e3-signotope-8-4-5-5.lrat")

end ErdosSzekeres

end
