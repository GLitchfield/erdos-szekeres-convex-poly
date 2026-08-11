module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof halfPureDeepSplitFin8_lrat_unsat
  (include_str "../certificates/half-pure-deep-split-fin8-core.cnf")
  (include_str "../certificates/half-pure-deep-split-fin8-core.lrat")

end ErdosSzekeres

end
