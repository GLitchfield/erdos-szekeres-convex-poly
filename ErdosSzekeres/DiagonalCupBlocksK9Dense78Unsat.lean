module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate for the normalized `7+8` k=9 core. -/

namespace ErdosSzekeres

lrat_proof diagonalCupBlocksK9Dense78_lrat_unsat
  (include_str "../certificates/k9-cup-blocks-7-8-dense.cnf")
  (include_str "../certificates/k9-cup-blocks-7-8-dense.lrat")

end ErdosSzekeres

end
