module

public import ErdosSzekeres.Extremal
public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate underlying the nine-point case. -/

namespace ErdosSzekeres

lrat_proof es5_signotope_unsat
  (include_str "../certificates/es5-signotope.cnf")
  (include_str "../certificates/es5-signotope.lrat")

end ErdosSzekeres

end
