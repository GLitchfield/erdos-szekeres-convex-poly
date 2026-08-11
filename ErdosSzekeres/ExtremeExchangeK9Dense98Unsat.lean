module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT proof for the dense `9-8` extreme-exchange core. -/

namespace ErdosSzekeres

lrat_proof extremeExchangeK9Dense98_lrat_unsat
  (include_str "../certificates/extreme-exchange-k9-9-8-dense.cnf")
  (include_str "../certificates/extreme-exchange-k9-9-8-dense.lrat")

end ErdosSzekeres

end
