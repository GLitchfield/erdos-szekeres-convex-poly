module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate for the twelve-vertex `(4,6,6)` state. -/

namespace ErdosSzekeres

lrat_proof e3State466_cnf_unsat
  (include_str "../certificates/e3-signotope-12-4-6-6.cnf")
  (include_str "../certificates/e3-signotope-12-4-6-6.lrat")

end ErdosSzekeres

end
