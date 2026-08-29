module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk056

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 073. -/

theorem predecessorHalfFin13_rejectSemanticSegment073
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi))) ∨
      ((PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      (¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0966 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0966 chi) ∨
      (PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0966 chi))) ∨
      ((PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0966 chi) ∨
      (PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi))) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi)))) ∨
      (((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi))) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0967 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi))))) ∨
      ((((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi))) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi)))) ∨
      (((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi))) ∨
      (((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0968 chi)) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi)))) ∨
      (((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi))) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      (¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi))) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi)))) ∨
      (((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi))) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi))) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi)))) ∨
      (((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0971 chi))) ∨
      (((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0971 chi)) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0971 chi))))))))) := by
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
              exact predecessorHalfFin13_clause16301 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16302 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16303 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16304 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16305 chi hbad
              ·
                exact predecessorHalfFin13_clause16306 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16312 chi hbad
              ·
                exact predecessorHalfFin13_clause16313 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16317 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16319 chi hbad
              ·
                exact predecessorHalfFin13_clause16320 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16321 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16322 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16323 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16324 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16325 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16326 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16327 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16328 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16329 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16330 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16332 chi hbad
              ·
                exact predecessorHalfFin13_clause16333 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16337 chi hbad
              ·
                exact predecessorHalfFin13_clause16341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16343 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16344 chi hbad
              ·
                exact predecessorHalfFin13_clause16345 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16346 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16347 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16348 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16350 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16351 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16352 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16353 chi hbad
              ·
                exact predecessorHalfFin13_clause16354 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16356 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16360 chi hbad
              ·
                exact predecessorHalfFin13_clause16361 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16364 chi hbad
              ·
                exact predecessorHalfFin13_clause16365 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16366 chi hbad
              ·
                exact predecessorHalfFin13_clause16367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16368 chi hbad
              ·
                exact predecessorHalfFin13_clause16369 chi hone hbad
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
              exact predecessorHalfFin13_clause16370 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16371 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16372 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16373 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16374 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16375 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16376 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16377 chi hbad
              ·
                exact predecessorHalfFin13_clause16378 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16380 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16382 chi hbad
              ·
                exact predecessorHalfFin13_clause16383 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16385 chi hbad
              ·
                exact predecessorHalfFin13_clause16389 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16392 chi hbad
              ·
                exact predecessorHalfFin13_clause16393 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16394 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16395 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16396 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16397 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16398 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16399 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16400 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16401 chi hbad
              ·
                exact predecessorHalfFin13_clause16402 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16404 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16408 chi hbad
              ·
                exact predecessorHalfFin13_clause16409 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16411 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16412 chi hbad
              ·
                exact predecessorHalfFin13_clause16413 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16416 chi hbad
              ·
                exact predecessorHalfFin13_clause16417 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16418 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16419 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16420 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16421 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16422 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16423 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16424 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16425 chi hbad
              ·
                exact predecessorHalfFin13_clause16426 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16428 chi hbad
              ·
                exact predecessorHalfFin13_clause16430 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16432 chi hbad
              ·
                exact predecessorHalfFin13_clause16433 chi hbad

end ErdosSzekeres

end
