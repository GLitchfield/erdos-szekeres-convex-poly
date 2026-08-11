module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof strongPredecessorFin8_lrat_unsat
  (include_str "../certificates/strong-predecessor-fin8-balanced.cnf")
  (include_str "../certificates/strong-predecessor-fin8-balanced.lrat")

end ErdosSzekeres

end
