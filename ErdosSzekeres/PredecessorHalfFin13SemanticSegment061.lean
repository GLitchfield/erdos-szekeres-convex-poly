module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk046
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk047

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 061. -/

theorem predecessorHalfFin13_rejectSemanticSegment061
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi))))) ∨
      ((((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi))) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi)))) ∨
      (((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi))) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi)) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi))) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi)))) ∨
      (((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi))) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi)) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      (¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi))) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi)))) ∨
      (((PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) ∨
      ((PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi))) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      (¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi))) ∨
      ((PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      ((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      (¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi))) ∨
      (((¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi)) ∨
      ((PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      (PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi))))))))) := by
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
              exact predecessorHalfFin13_clause14657 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14659 chi hbad
              ·
                exact predecessorHalfFin13_clause14661 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14663 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14664 chi hbad
              ·
                exact predecessorHalfFin13_clause14665 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14666 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14667 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14668 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14669 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14670 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14671 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14672 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14673 chi hbad
              ·
                exact predecessorHalfFin13_clause14674 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14677 chi hbad
              ·
                exact predecessorHalfFin13_clause14680 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14681 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14685 chi hbad
              ·
                exact predecessorHalfFin13_clause14687 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14689 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14690 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14691 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14692 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14693 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14694 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14695 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14696 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14698 chi hbad
              ·
                exact predecessorHalfFin13_clause14699 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14701 chi hbad
              ·
                exact predecessorHalfFin13_clause14702 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14705 chi hbad
              ·
                exact predecessorHalfFin13_clause14707 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14709 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14711 chi hbad
              ·
                exact predecessorHalfFin13_clause14712 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14713 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14714 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14715 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14716 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14717 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14718 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14719 chi hone hbad
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
              exact predecessorHalfFin13_clause14720 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14721 chi hbad
              ·
                exact predecessorHalfFin13_clause14722 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14728 chi hbad
              ·
                exact predecessorHalfFin13_clause14729 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14733 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14735 chi hbad
              ·
                exact predecessorHalfFin13_clause14736 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14737 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14738 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14739 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14740 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14741 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14742 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14743 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14744 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14745 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14748 chi hbad
              ·
                exact predecessorHalfFin13_clause14750 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14752 chi hbad
              ·
                exact predecessorHalfFin13_clause14753 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14757 chi hbad
              ·
                exact predecessorHalfFin13_clause14759 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14761 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14762 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14763 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14764 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14765 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14766 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14767 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14768 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14770 chi hbad
              ·
                exact predecessorHalfFin13_clause14772 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14774 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14776 chi hbad
              ·
                exact predecessorHalfFin13_clause14777 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14783 chi hbad
              ·
                exact predecessorHalfFin13_clause14784 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14785 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14786 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14787 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14788 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14789 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14790 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14791 chi hone hbad

end ErdosSzekeres

end
