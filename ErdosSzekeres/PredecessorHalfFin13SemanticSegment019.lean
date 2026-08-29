module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk014
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk015

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 019. -/

theorem predecessorHalfFin13_rejectSemanticSegment019
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi))) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi)))) ∨
      (((PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi))) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi))))) ∨
      ((((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi))) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi))) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi))) ∨
      ((¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) ∨
      ((¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) ∨
      (¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) ∨
      ((PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      (PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi))) ∨
      ((PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      ((PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      (¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) ∨
      ((¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) ∨
      (¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))) ∨
      ((¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) ∨
      ((¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) ∨
      (PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi)))) ∨
      (((PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) ∨
      ((PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) ∨
      (PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))) ∨
      (((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi)) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi))) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi))) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0487 chi))))) ∨
      ((((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi))) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi)))) ∨
      (((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi))) ∨
      (((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi)) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi))) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0488 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi))) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi))))) ∨
      ((((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi))) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) ∨
      ((¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi))) ∨
      (((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0490 chi)) ∨
      ((PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi))))))))) := by
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
              exact predecessorHalfFin13_clause04665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04666 chi hbad
              ·
                exact predecessorHalfFin13_clause04668 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04673 chi hbad
              ·
                exact predecessorHalfFin13_clause04677 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04680 chi hbad
              ·
                exact predecessorHalfFin13_clause04705 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04706 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04707 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04708 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04709 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04710 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04711 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04712 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04713 chi hbad
              ·
                exact predecessorHalfFin13_clause04714 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04715 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04716 chi hbad
              ·
                exact predecessorHalfFin13_clause04718 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04721 chi hbad
              ·
                exact predecessorHalfFin13_clause04725 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04727 chi hbad
              ·
                exact predecessorHalfFin13_clause04728 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04753 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04754 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04755 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04756 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04757 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04758 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04759 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04760 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04761 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04763 chi hbad
              ·
                exact predecessorHalfFin13_clause04764 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04768 chi hbad
              ·
                exact predecessorHalfFin13_clause04769 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04773 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04775 chi hbad
              ·
                exact predecessorHalfFin13_clause04776 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04801 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04802 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04803 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04804 chi hone hbad
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
              exact predecessorHalfFin13_clause04805 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04806 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04807 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04808 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04809 chi hbad
              ·
                exact predecessorHalfFin13_clause04810 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04812 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04814 chi hbad
              ·
                exact predecessorHalfFin13_clause04816 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04821 chi hbad
              ·
                exact predecessorHalfFin13_clause04823 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04825 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04826 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04827 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04828 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04829 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04830 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04831 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04832 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04833 chi hbad
              ·
                exact predecessorHalfFin13_clause04834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04835 chi hbad
              ·
                exact predecessorHalfFin13_clause04836 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04840 chi hbad
              ·
                exact predecessorHalfFin13_clause04841 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04845 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04847 chi hbad
              ·
                exact predecessorHalfFin13_clause04848 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04873 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04874 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04875 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04876 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04877 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04878 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04879 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04880 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04881 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04884 chi hbad
              ·
                exact predecessorHalfFin13_clause04886 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04889 chi hbad
              ·
                exact predecessorHalfFin13_clause04892 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04893 chi hbad
              ·
                exact predecessorHalfFin13_clause04895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04896 chi hbad
              ·
                exact predecessorHalfFin13_clause04897 chi hone hbad

end ErdosSzekeres

end
