module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk013
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk014

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 018. -/

theorem predecessorHalfFin13_rejectSemanticSegment018
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi)))) ∨
      (((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi))) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi)))) ∨
      (((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi))) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi))))) ∨
      ((((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi))) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi)))) ∨
      (((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi))) ∨
      (((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi)) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi))) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi))) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi))))) ∨
      ((((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi))) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi))) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi))) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi)))) ∨
      (((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi))) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) ∨
      ((¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      (¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) ∨
      (PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi))) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) ∨
      ((PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) ∨
      ((¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) ∨
      (¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi))) ∨
      (((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi)) ∨
      ((PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) ∨
      (PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi))))))))) := by
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
              exact predecessorHalfFin13_clause04488 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04489 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04490 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04491 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04492 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04493 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04494 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04495 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04496 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04498 chi hbad
              ·
                exact predecessorHalfFin13_clause04500 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04502 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04504 chi hbad
              ·
                exact predecessorHalfFin13_clause04505 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04508 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04509 chi hbad
              ·
                exact predecessorHalfFin13_clause04511 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04537 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04538 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04539 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04540 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04541 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04542 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04543 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04544 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04545 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04546 chi hbad
              ·
                exact predecessorHalfFin13_clause04547 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04550 chi hbad
              ·
                exact predecessorHalfFin13_clause04552 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04553 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04557 chi hbad
              ·
                exact predecessorHalfFin13_clause04559 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04561 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04562 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04563 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04564 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04565 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04566 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04567 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04568 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04569 chi hbad
              ·
                exact predecessorHalfFin13_clause04570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04571 chi hbad
              ·
                exact predecessorHalfFin13_clause04572 chi hbad
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
              exact predecessorHalfFin13_clause04576 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04577 chi hbad
              ·
                exact predecessorHalfFin13_clause04581 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04584 chi hbad
              ·
                exact predecessorHalfFin13_clause04585 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04586 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04587 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04588 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04589 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04590 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04591 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04592 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04593 chi hbad
              ·
                exact predecessorHalfFin13_clause04594 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04595 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04596 chi hbad
              ·
                exact predecessorHalfFin13_clause04598 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04600 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04601 chi hbad
              ·
                exact predecessorHalfFin13_clause04605 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04608 chi hbad
              ·
                exact predecessorHalfFin13_clause04633 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04634 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04635 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04636 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04637 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04638 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04639 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04640 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04641 chi hbad
              ·
                exact predecessorHalfFin13_clause04642 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04643 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04644 chi hbad
              ·
                exact predecessorHalfFin13_clause04646 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04649 chi hbad
              ·
                exact predecessorHalfFin13_clause04653 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04656 chi hbad
              ·
                exact predecessorHalfFin13_clause04657 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04658 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04659 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04660 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04661 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04662 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04663 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04664 chi hone hbad

end ErdosSzekeres

end
