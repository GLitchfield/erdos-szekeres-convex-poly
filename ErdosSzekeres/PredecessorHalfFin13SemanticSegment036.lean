module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk027
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk028

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 036. -/

theorem predecessorHalfFin13_rejectSemanticSegment036
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0756 chi) ∨
      ((PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0756 chi) ∨
      (PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi))) ∨
      ((PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0756 chi) ∨
      ((PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi))))) ∨
      ((((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0757 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0758 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi))) ∨
      (((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi)) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0759 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0759 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0759 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0759 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0759 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0760 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0760 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0760 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0760 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi))) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0761 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      ((¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0761 chi) ∨
      (¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0761 chi))) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0761 chi) ∨
      ((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0761 chi)))) ∨
      (((PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      ((¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      (¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi))) ∨
      (((¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      (¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi)) ∨
      ((PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      (PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi))))))))) := by
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
              exact predecessorHalfFin13_clause11272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11273 chi hbad
              ·
                exact predecessorHalfFin13_clause11277 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11279 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11280 chi hbad
              ·
                exact predecessorHalfFin13_clause11281 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11282 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11283 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11284 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11285 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11286 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11287 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11288 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11289 chi hbad
              ·
                exact predecessorHalfFin13_clause11290 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11296 chi hbad
              ·
                exact predecessorHalfFin13_clause11297 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11299 chi hbad
              ·
                exact predecessorHalfFin13_clause11300 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11301 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11302 chi hbad
              ·
                exact predecessorHalfFin13_clause11303 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11305 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11306 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11307 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11308 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11309 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11310 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11311 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11312 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11313 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11314 chi hbad
              ·
                exact predecessorHalfFin13_clause11315 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11316 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11320 chi hbad
              ·
                exact predecessorHalfFin13_clause11321 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11323 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11325 chi hbad
              ·
                exact predecessorHalfFin13_clause11327 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11329 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11330 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11331 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11332 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11333 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11334 chi hone hbad
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
              exact predecessorHalfFin13_clause11335 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11336 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11337 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11338 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11340 chi hbad
              ·
                exact predecessorHalfFin13_clause11342 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11345 chi hbad
              ·
                exact predecessorHalfFin13_clause11349 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11351 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11352 chi hbad
              ·
                exact predecessorHalfFin13_clause11353 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11354 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11355 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11356 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11357 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11358 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11359 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11360 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11361 chi hbad
              ·
                exact predecessorHalfFin13_clause11362 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11369 chi hbad
              ·
                exact predecessorHalfFin13_clause11373 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11376 chi hbad
              ·
                exact predecessorHalfFin13_clause11377 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11378 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11379 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11380 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11381 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11382 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11383 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11384 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11385 chi hbad
              ·
                exact predecessorHalfFin13_clause11386 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11390 chi hbad
              ·
                exact predecessorHalfFin13_clause11392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11397 chi hbad
              ·
                exact predecessorHalfFin13_clause11399 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11400 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11401 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11402 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11403 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11404 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11405 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11406 chi hone hbad

end ErdosSzekeres

end
