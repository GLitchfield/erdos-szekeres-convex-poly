import ErdosSzekeres.Extremal
import Mathlib.Tactic.Sat.FromLRAT

/-! Kernel-checked LRAT certificate underlying the nine-point case. -/

namespace ErdosSzekeres

lrat_proof es5_signotope_unsat
  (include_str "../certificates/es5-signotope.cnf")
  (include_str "../certificates/es5-signotope.lrat")

end ErdosSzekeres
