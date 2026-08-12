module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof halfPureSingletonFanFin10_lrat_unsat
  (include_str "../runs/agents/20260811-four-slot-deep-wave/half-pure-fin10/half-pure-singleton-fin10-core.cnf")
  (include_str "../runs/agents/20260811-four-slot-deep-wave/half-pure-fin10/half-pure-singleton-fin10-core.lrat")

end ErdosSzekeres

end
