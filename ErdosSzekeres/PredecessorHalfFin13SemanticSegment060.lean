module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk046

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 060. -/

theorem predecessorHalfFin13_rejectSemanticSegment060
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      (PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi))) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      (¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      (¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi))) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi) ∨
      (PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi))))) ∨
      ((((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0892 chi) ∨
      (PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi))) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      (¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      (PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi))) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      (¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      (¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0893 chi))) ∨
      ((¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi)))) ∨
      (((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      ((PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi))) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi))))) ∨
      ((((PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) ∨
      (PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi))) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0894 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0894 chi) ∨
      (PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0894 chi))) ∨
      (((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0894 chi)) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi))) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      (PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi)))) ∨
      (((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi))) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      ((¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      (¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      (PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi))) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      ((PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      (¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) ∨
      ((¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      (¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi))) ∨
      ((PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      ((PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) ∨
      (PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      ((¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      (¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi))) ∨
      ((¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      ((¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi) ∨
      (¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi)))) ∨
      (((PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi) ∨
      ((PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      (PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi))) ∨
      ((PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0896 chi) ∨
      ((PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi))) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      (PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi)))) ∨
      (((PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi))) ∨
      (((¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi)) ∨
      ((¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      (¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0897 chi))))))))) := by
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
              exact predecessorHalfFin13_clause14524 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14525 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14526 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14527 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14528 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14529 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14532 chi hbad
              ·
                exact predecessorHalfFin13_clause14534 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14536 chi hbad
              ·
                exact predecessorHalfFin13_clause14537 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14543 chi hbad
              ·
                exact predecessorHalfFin13_clause14544 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14545 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14546 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14547 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14548 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14549 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14550 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14551 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14552 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14553 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14556 chi hbad
              ·
                exact predecessorHalfFin13_clause14558 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14561 chi hbad
              ·
                exact predecessorHalfFin13_clause14565 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14568 chi hbad
              ·
                exact predecessorHalfFin13_clause14569 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14570 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14571 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14572 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14573 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14574 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14575 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14576 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14577 chi hbad
              ·
                exact predecessorHalfFin13_clause14578 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14580 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14584 chi hbad
              ·
                exact predecessorHalfFin13_clause14585 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14589 chi hbad
              ·
                exact predecessorHalfFin13_clause14591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14592 chi hbad
              ·
                exact predecessorHalfFin13_clause14593 chi hone hbad
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
              exact predecessorHalfFin13_clause14594 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14595 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14596 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14597 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14598 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14599 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14600 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14601 chi hbad
              ·
                exact predecessorHalfFin13_clause14602 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14603 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14604 chi hbad
              ·
                exact predecessorHalfFin13_clause14607 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14608 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14609 chi hbad
              ·
                exact predecessorHalfFin13_clause14613 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14616 chi hbad
              ·
                exact predecessorHalfFin13_clause14617 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14618 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14619 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14620 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14621 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14622 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14623 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14624 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14625 chi hbad
              ·
                exact predecessorHalfFin13_clause14626 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14629 chi hbad
              ·
                exact predecessorHalfFin13_clause14632 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14637 chi hbad
              ·
                exact predecessorHalfFin13_clause14638 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14640 chi hbad
              ·
                exact predecessorHalfFin13_clause14641 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14642 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14643 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14644 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14645 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14646 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14647 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14648 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14649 chi hbad
              ·
                exact predecessorHalfFin13_clause14650 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14651 chi hbad
              ·
                exact predecessorHalfFin13_clause14652 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14655 chi hbad
              ·
                exact predecessorHalfFin13_clause14656 chi hbad

end ErdosSzekeres

end
