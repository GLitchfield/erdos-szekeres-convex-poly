module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT proof for the dense `8-9` extreme-exchange core. -/

namespace ErdosSzekeres

lrat_proof extremeExchangeK9Dense89_lrat_unsat
  (include_str "../certificates/extreme-exchange-k9-8-9-dense.cnf")
  (include_str "../certificates/extreme-exchange-k9-8-9-dense.lrat")

end ErdosSzekeres

end
