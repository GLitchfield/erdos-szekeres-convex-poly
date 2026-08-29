module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof halfPureSingletonFanFin10_lrat_unsat
  (include_str "../certificates/half-pure-singleton-fin10/half-pure-singleton-fin10-core.cnf")
  (include_str "../certificates/half-pure-singleton-fin10/half-pure-singleton-fin10-core.lrat")

end ErdosSzekeres

end
