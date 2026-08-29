module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk016

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 021. -/

theorem predecessorHalfFin13_rejectSemanticSegment021
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) ∨
      ((PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      (PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi))) ∨
      ((PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      ((¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      ((¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi))) ∨
      ((PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      ((PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      ((¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) ∨
      (¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi))) ∨
      ((¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      ((¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi)))) ∨
      (((PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) ∨
      ((PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi))) ∨
      ((PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi))))) ∨
      ((((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi))) ∨
      (((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi)) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi)))) ∨
      (((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi)))) ∨
      (((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi)) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi))))))))) := by
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
              exact predecessorHalfFin13_clause05156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05157 chi hbad
              ·
                exact predecessorHalfFin13_clause05159 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05160 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05209 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05210 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05211 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05212 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05213 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05214 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05215 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05216 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05218 chi hbad
              ·
                exact predecessorHalfFin13_clause05219 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05224 chi hbad
              ·
                exact predecessorHalfFin13_clause05225 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05228 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05229 chi hbad
              ·
                exact predecessorHalfFin13_clause05231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09241 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09242 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09243 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09244 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09245 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09246 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09247 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09248 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09250 chi hbad
              ·
                exact predecessorHalfFin13_clause09252 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09254 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09256 chi hbad
              ·
                exact predecessorHalfFin13_clause09257 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09258 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09260 chi hbad
              ·
                exact predecessorHalfFin13_clause09261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09263 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09264 chi hbad
              ·
                exact predecessorHalfFin13_clause09265 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09266 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09267 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09268 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09269 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09270 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09271 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09272 chi hone hbad
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
              exact predecessorHalfFin13_clause09273 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09274 chi hbad
              ·
                exact predecessorHalfFin13_clause09276 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09281 chi hbad
              ·
                exact predecessorHalfFin13_clause09283 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09285 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09287 chi hbad
              ·
                exact predecessorHalfFin13_clause09288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09289 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09290 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09291 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09292 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09293 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09294 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09295 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09296 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09297 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09299 chi hbad
              ·
                exact predecessorHalfFin13_clause09300 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09305 chi hbad
              ·
                exact predecessorHalfFin13_clause09306 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09309 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09310 chi hbad
              ·
                exact predecessorHalfFin13_clause09311 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09312 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09313 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09314 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09315 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09316 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09317 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09318 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09319 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09320 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09321 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09322 chi hbad
              ·
                exact predecessorHalfFin13_clause09324 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09329 chi hbad
              ·
                exact predecessorHalfFin13_clause09333 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09334 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09335 chi hbad
              ·
                exact predecessorHalfFin13_clause09336 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09337 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09338 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09339 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09340 chi hone hbad

end ErdosSzekeres

end
