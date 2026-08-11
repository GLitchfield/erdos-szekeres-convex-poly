module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate for the normalized `8+7` k=9 core. -/

namespace ErdosSzekeres

lrat_proof diagonalCupBlocksK9Dense87_lrat_unsat
  (include_str "../certificates/k9-cup-blocks-8-7-dense.cnf")
  (include_str "../certificates/k9-cup-blocks-8-7-dense.lrat")

end ErdosSzekeres

end
