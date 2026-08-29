module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk055
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk056

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 072. -/

theorem predecessorHalfFin13_rejectSemanticSegment072
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) ∨
      (PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi))) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) ∨
      (PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      ((¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      (¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi))) ∨
      ((¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      (PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi))))) ∨
      ((((PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      (¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi))) ∨
      ((¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      ((¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      (¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi))) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      ((PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      (¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) ∨
      ((¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      (¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi))) ∨
      ((PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      ((PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) ∨
      (PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi)))) ∨
      (((PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      ((¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) ∨
      (¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi))) ∨
      ((¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) ∨
      ((PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) ∨
      (PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi))))) ∨
      ((((PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) ∨
      ((PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) ∨
      (PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi))) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      (¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi))) ∨
      (((PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi)) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      (¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      (¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi))) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi)))) ∨
      (((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi))) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi))) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      (¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi))) ∨
      ((¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      (PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi))) ∨
      ((PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      ((¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      (¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      ((¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi))) ∨
      ((PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      ((PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      ((¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) ∨
      (¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi))) ∨
      ((¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) ∨
      ((¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) ∨
      (PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi)))) ∨
      (((PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      ((PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) ∨
      (PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi))) ∨
      (((¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi)) ∨
      ((¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))))))))) := by
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
              exact predecessorHalfFin13_clause16168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16169 chi hbad
              ·
                exact predecessorHalfFin13_clause16171 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16173 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16175 chi hbad
              ·
                exact predecessorHalfFin13_clause16176 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16177 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16178 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16179 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16180 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16181 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16182 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16183 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16184 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16185 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16188 chi hbad
              ·
                exact predecessorHalfFin13_clause16189 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16193 chi hbad
              ·
                exact predecessorHalfFin13_clause16197 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16200 chi hbad
              ·
                exact predecessorHalfFin13_clause16201 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16202 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16203 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16204 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16205 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16206 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16207 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16208 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16209 chi hbad
              ·
                exact predecessorHalfFin13_clause16210 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16212 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16217 chi hbad
              ·
                exact predecessorHalfFin13_clause16219 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16221 chi hbad
              ·
                exact predecessorHalfFin13_clause16224 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16225 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16226 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16227 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16228 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16229 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16230 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16231 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16232 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16233 chi hbad
              ·
                exact predecessorHalfFin13_clause16234 chi hbad
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
              exact predecessorHalfFin13_clause16235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16236 chi hbad
              ·
                exact predecessorHalfFin13_clause16237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16240 chi hbad
              ·
                exact predecessorHalfFin13_clause16241 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16246 chi hbad
              ·
                exact predecessorHalfFin13_clause16247 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16248 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16249 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16250 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16251 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16252 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16253 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16254 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16255 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16256 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16258 chi hbad
              ·
                exact predecessorHalfFin13_clause16260 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16264 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16265 chi hbad
              ·
                exact predecessorHalfFin13_clause16266 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16269 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16270 chi hbad
              ·
                exact predecessorHalfFin13_clause16271 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16273 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16274 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16275 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16276 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16277 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16278 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16279 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16280 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16282 chi hbad
              ·
                exact predecessorHalfFin13_clause16284 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16288 chi hbad
              ·
                exact predecessorHalfFin13_clause16289 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16293 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16295 chi hbad
              ·
                exact predecessorHalfFin13_clause16296 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16297 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16298 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16299 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16300 chi hone hbad

end ErdosSzekeres

end
