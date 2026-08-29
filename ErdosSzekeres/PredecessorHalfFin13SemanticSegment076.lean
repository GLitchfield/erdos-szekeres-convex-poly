module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk058
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk059

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 076. -/

theorem predecessorHalfFin13_rejectSemanticSegment076
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      (PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi))) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      (PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      (¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi))) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      (PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi))))) ∨
      ((((PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      (¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi))) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      (¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi)))) ∨
      (((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi))) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      (¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi))) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      ((PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi)))) ∨
      (((PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      (¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi))) ∨
      ((¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      ((¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi))))) ∨
      ((((PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      ((PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi))) ∨
      ((¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) ∨
      ((¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) ∨
      (¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) ∨
      ((PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) ∨
      (PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi))) ∨
      (((PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) ∨
      (PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi)) ∨
      ((PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) ∨
      (¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))) ∨
      ((PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi)))) ∨
      (((PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      (¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi))) ∨
      ((¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      ((¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) ∨
      (PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi))))) ∨
      ((((PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      ((PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) ∨
      (PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi))) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi))) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi))) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi)))) ∨
      (((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi))) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi))) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      (PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi)))) ∨
      (((PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      ((PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi))) ∨
      (((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi)) ∨
      ((¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) ∨
      (¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi))))))))) := by
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
              exact predecessorHalfFin13_clause16707 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16708 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16709 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16710 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16711 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16712 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16714 chi hbad
              ·
                exact predecessorHalfFin13_clause16716 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16721 chi hbad
              ·
                exact predecessorHalfFin13_clause16725 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16727 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16728 chi hbad
              ·
                exact predecessorHalfFin13_clause16729 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16730 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16731 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16732 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16733 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16734 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16735 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16736 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16737 chi hbad
              ·
                exact predecessorHalfFin13_clause16738 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16743 chi hbad
              ·
                exact predecessorHalfFin13_clause16744 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16749 chi hbad
              ·
                exact predecessorHalfFin13_clause16751 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16753 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16754 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16755 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16756 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16757 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16758 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16759 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16760 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16762 chi hbad
              ·
                exact predecessorHalfFin13_clause16764 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16768 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16769 chi hbad
              ·
                exact predecessorHalfFin13_clause16772 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16773 chi hbad
              ·
                exact predecessorHalfFin13_clause16775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16776 chi hbad
              ·
                exact predecessorHalfFin13_clause16777 chi hone hbad
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
              exact predecessorHalfFin13_clause16778 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16779 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16780 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16781 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16782 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16783 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16784 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16785 chi hbad
              ·
                exact predecessorHalfFin13_clause16786 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16788 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16792 chi hbad
              ·
                exact predecessorHalfFin13_clause16793 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16799 chi hbad
              ·
                exact predecessorHalfFin13_clause16800 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16801 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16802 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16803 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16804 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16805 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16806 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16807 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16808 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16809 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16811 chi hbad
              ·
                exact predecessorHalfFin13_clause16812 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16815 chi hbad
              ·
                exact predecessorHalfFin13_clause16816 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16819 chi hbad
              ·
                exact predecessorHalfFin13_clause16821 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16822 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16823 chi hbad
              ·
                exact predecessorHalfFin13_clause16824 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16825 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16826 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16827 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16828 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16829 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16830 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16831 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16832 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16833 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16834 chi hbad
              ·
                exact predecessorHalfFin13_clause16835 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16836 chi hbad
              ·
                exact predecessorHalfFin13_clause16837 chi hbad

end ErdosSzekeres

end
