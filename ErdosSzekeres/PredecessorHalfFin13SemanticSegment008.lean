module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk006

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 008. -/

theorem predecessorHalfFin13_rejectSemanticSegment008
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0397 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0397 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0397 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0397 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0397 chi))))) ∨
      ((((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi)))) ∨
      (((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0398 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0398 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0398 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0398 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi))))) ∨
      ((((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0399 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0399 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0399 chi)))) ∨
      (((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0399 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0399 chi))) ∨
      (((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi)) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi))))) ∨
      ((((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0401 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0402 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0402 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0402 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0402 chi)))) ∨
      (((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0402 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0403 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0403 chi))) ∨
      (((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0403 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi)) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0403 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02645 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02646 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02647 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02648 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02649 chi hbad
              ·
                exact predecessorHalfFin13_clause02650 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02651 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02652 chi hbad
              ·
                exact predecessorHalfFin13_clause02656 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02657 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02661 chi hbad
              ·
                exact predecessorHalfFin13_clause02663 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02665 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02666 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02667 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02668 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02669 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02670 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02671 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02672 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02674 chi hbad
              ·
                exact predecessorHalfFin13_clause02676 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02681 chi hbad
              ·
                exact predecessorHalfFin13_clause02685 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02687 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02688 chi hbad
              ·
                exact predecessorHalfFin13_clause02689 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02690 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02691 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02692 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02693 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02694 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02695 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02696 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02697 chi hbad
              ·
                exact predecessorHalfFin13_clause02698 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02704 chi hbad
              ·
                exact predecessorHalfFin13_clause02705 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02707 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02709 chi hbad
              ·
                exact predecessorHalfFin13_clause02711 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02712 chi hbad
              ·
                exact predecessorHalfFin13_clause02737 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02738 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02739 chi hone hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02740 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02741 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02742 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02743 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02744 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02745 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02747 chi hbad
              ·
                exact predecessorHalfFin13_clause02748 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02753 chi hbad
              ·
                exact predecessorHalfFin13_clause02755 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02757 chi hbad
              ·
                exact predecessorHalfFin13_clause02759 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02761 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02762 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02763 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02764 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02765 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02766 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02767 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02768 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02770 chi hbad
              ·
                exact predecessorHalfFin13_clause02772 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02776 chi hbad
              ·
                exact predecessorHalfFin13_clause02777 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02783 chi hbad
              ·
                exact predecessorHalfFin13_clause02784 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02785 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02786 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02787 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02788 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02789 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02790 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02791 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02792 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02793 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02794 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02796 chi hbad
              ·
                exact predecessorHalfFin13_clause02800 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02801 chi hbad
              ·
                exact predecessorHalfFin13_clause02805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02807 chi hbad
              ·
                exact predecessorHalfFin13_clause02808 chi hbad

end ErdosSzekeres

end
