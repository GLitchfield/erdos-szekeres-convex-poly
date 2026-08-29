module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk006
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk007

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 009. -/

theorem predecessorHalfFin13_rejectSemanticSegment009
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi)))) ∨
      (((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi))))) ∨
      ((((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0404 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi)))) ∨
      (((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi))) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi)))) ∨
      (((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi))) ∨
      (((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi)) ∨
      ((¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi))) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0407 chi) ∨
      ((PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi))) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi))))) ∨
      ((((PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi))) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi)))) ∨
      (((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0408 chi))) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi))) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi))) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi))))) ∨
      ((((PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0409 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi))) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi) ∨
      ((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi))) ∨
      (((PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi) ∨
      (PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi)) ∨
      ((¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      (¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0410 chi))))))))) := by
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
              exact predecessorHalfFin13_clause02809 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02810 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02811 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02812 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02813 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02814 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02815 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02816 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02817 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02818 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02820 chi hbad
              ·
                exact predecessorHalfFin13_clause02824 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02825 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02827 chi hbad
              ·
                exact predecessorHalfFin13_clause02829 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02831 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02832 chi hbad
              ·
                exact predecessorHalfFin13_clause02833 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02834 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02835 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02836 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02837 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02838 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02839 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02840 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02841 chi hbad
              ·
                exact predecessorHalfFin13_clause02842 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02843 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02844 chi hbad
              ·
                exact predecessorHalfFin13_clause02848 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02849 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02851 chi hbad
              ·
                exact predecessorHalfFin13_clause02852 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02853 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02855 chi hbad
              ·
                exact predecessorHalfFin13_clause02856 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02881 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02882 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02883 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02884 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02885 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02886 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02887 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02888 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02889 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02890 chi hbad
              ·
                exact predecessorHalfFin13_clause02891 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02892 chi hbad
              ·
                exact predecessorHalfFin13_clause02896 chi hbad
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
              exact predecessorHalfFin13_clause02897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02900 chi hbad
              ·
                exact predecessorHalfFin13_clause02901 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02903 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02904 chi hbad
              ·
                exact predecessorHalfFin13_clause02905 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02906 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02907 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02908 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02909 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02910 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02911 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02912 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02913 chi hbad
              ·
                exact predecessorHalfFin13_clause02914 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02916 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02920 chi hbad
              ·
                exact predecessorHalfFin13_clause02921 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02924 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02925 chi hbad
              ·
                exact predecessorHalfFin13_clause02927 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02928 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02929 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02930 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02931 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02932 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02933 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02934 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02935 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02936 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02937 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02938 chi hbad
              ·
                exact predecessorHalfFin13_clause02939 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02940 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02944 chi hbad
              ·
                exact predecessorHalfFin13_clause02945 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02951 chi hbad
              ·
                exact predecessorHalfFin13_clause02952 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02953 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02954 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02955 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02956 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02957 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02958 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02959 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02960 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02961 chi hbad
              ·
                exact predecessorHalfFin13_clause02962 chi hbad

end ErdosSzekeres

end
