module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk015
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk016

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 020. -/

theorem predecessorHalfFin13_rejectSemanticSegment020
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi))) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi)))) ∨
      (((PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi))) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi))))) ∨
      ((((PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0491 chi))) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi))) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) ∨
      (¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi))) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) ∨
      ((¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi)))) ∨
      (((PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) ∨
      ((PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0493 chi) ∨
      (PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi))) ∨
      ((¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi))) ∨
      ((PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) ∨
      ((¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      (¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi))) ∨
      (((PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) ∨
      (PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi)) ∨
      ((PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0495 chi) ∨
      (PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi))) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi)))) ∨
      (((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi))) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) ∨
      (PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi))) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0497 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi))) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      (PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi))) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      ((¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) ∨
      (¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi)))) ∨
      (((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) ∨
      (PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi))) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) ∨
      ((PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) ∨
      (PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      ((¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      (¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi))) ∨
      ((¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      ((PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      (PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi)))) ∨
      (((PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      ((PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      (¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi))) ∨
      (((¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) ∨
      (¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi)) ∨
      ((¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) ∨
      (PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi))))))))) := by
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
              exact predecessorHalfFin13_clause04898 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04899 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04900 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04901 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04902 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04903 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04904 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04905 chi hbad
              ·
                exact predecessorHalfFin13_clause04906 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04910 chi hbad
              ·
                exact predecessorHalfFin13_clause04912 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04917 chi hbad
              ·
                exact predecessorHalfFin13_clause04919 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04945 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04946 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04947 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04948 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04949 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04950 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04951 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04952 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04953 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04954 chi hbad
              ·
                exact predecessorHalfFin13_clause04956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04958 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04960 chi hbad
              ·
                exact predecessorHalfFin13_clause04961 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04965 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04967 chi hbad
              ·
                exact predecessorHalfFin13_clause04968 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04993 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04994 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04995 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04996 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04997 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04998 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04999 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05000 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05001 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05004 chi hbad
              ·
                exact predecessorHalfFin13_clause05008 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05009 chi hbad
              ·
                exact predecessorHalfFin13_clause05013 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05015 chi hbad
              ·
                exact predecessorHalfFin13_clause05016 chi hbad
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
              exact predecessorHalfFin13_clause05041 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05042 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05043 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05044 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05045 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05046 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05047 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05048 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05049 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05050 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05052 chi hbad
              ·
                exact predecessorHalfFin13_clause05054 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05056 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05057 chi hbad
              ·
                exact predecessorHalfFin13_clause05061 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05063 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05064 chi hbad
              ·
                exact predecessorHalfFin13_clause05089 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05090 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05091 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05092 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05093 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05094 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05095 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05096 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05097 chi hbad
              ·
                exact predecessorHalfFin13_clause05098 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05102 chi hbad
              ·
                exact predecessorHalfFin13_clause05104 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05105 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05106 chi hbad
              ·
                exact predecessorHalfFin13_clause05109 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05111 chi hbad
              ·
                exact predecessorHalfFin13_clause05112 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05137 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05138 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05139 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05140 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05141 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05142 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause05143 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05144 chi hone hbad
              ·
                exact predecessorHalfFin13_clause05145 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05146 chi hbad
              ·
                exact predecessorHalfFin13_clause05148 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause05152 chi hbad
              ·
                exact predecessorHalfFin13_clause05153 chi hbad

end ErdosSzekeres

end
