module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk052

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 068. -/

theorem predecessorHalfFin13_rejectSemanticSegment068
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi))) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi)))) ∨
      (((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi))) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi))) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi))) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi))) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi)))) ∨
      (((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi))) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi))))) ∨
      ((((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi))) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi))) ∨
      (((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi)) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi))) ∨
      ((¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi)))) ∨
      (((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi))) ∨
      ((PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi))) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi))) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi))) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi)))) ∨
      (((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi))) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi))) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi))) ∨
      (((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi)) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi))))))))) := by
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
              exact predecessorHalfFin13_clause15610 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15612 chi hbad
              ·
                exact predecessorHalfFin13_clause15614 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15616 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15617 chi hbad
              ·
                exact predecessorHalfFin13_clause15619 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15623 chi hbad
              ·
                exact predecessorHalfFin13_clause15624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15625 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15626 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15627 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15628 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15629 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15630 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15631 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15632 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15633 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15636 chi hbad
              ·
                exact predecessorHalfFin13_clause15640 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15645 chi hbad
              ·
                exact predecessorHalfFin13_clause15647 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15649 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15650 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15651 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15652 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15653 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15654 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15655 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15656 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15658 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15662 chi hbad
              ·
                exact predecessorHalfFin13_clause15664 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15669 chi hbad
              ·
                exact predecessorHalfFin13_clause15671 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15673 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15674 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15675 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15676 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15677 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15678 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15679 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15680 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15681 chi hbad
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
              exact predecessorHalfFin13_clause15682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15684 chi hbad
              ·
                exact predecessorHalfFin13_clause15686 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15689 chi hbad
              ·
                exact predecessorHalfFin13_clause15691 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15693 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15694 chi hbad
              ·
                exact predecessorHalfFin13_clause15695 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15696 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15697 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15698 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15699 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15700 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15701 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15702 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15703 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15704 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15706 chi hbad
              ·
                exact predecessorHalfFin13_clause15708 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15712 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15713 chi hbad
              ·
                exact predecessorHalfFin13_clause15717 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15719 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15720 chi hbad
              ·
                exact predecessorHalfFin13_clause15721 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15722 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15723 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15724 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15725 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15726 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15727 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15728 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15730 chi hbad
              ·
                exact predecessorHalfFin13_clause15732 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15737 chi hbad
              ·
                exact predecessorHalfFin13_clause15741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15743 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15744 chi hbad
              ·
                exact predecessorHalfFin13_clause15745 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15746 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15747 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15748 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15749 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15750 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15751 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15752 chi hone hbad

end ErdosSzekeres

end
