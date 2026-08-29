module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk000
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk001

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 001. -/

theorem predecessorHalfFin13_rejectSemanticSegment001
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0347 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi))))) ∨
      ((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi))))) ∨
      ((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0350 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi)) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi)))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0351 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0352 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi)))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0353 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi)) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi))))))))) := by
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
              exact predecessorHalfFin13_clause01450 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01452 chi hbad
              ·
                exact predecessorHalfFin13_clause01456 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01461 chi hbad
              ·
                exact predecessorHalfFin13_clause01463 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01464 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01465 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01466 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01467 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01468 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01469 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01470 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01471 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01472 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01474 chi hbad
              ·
                exact predecessorHalfFin13_clause01476 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01481 chi hbad
              ·
                exact predecessorHalfFin13_clause01483 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01487 chi hbad
              ·
                exact predecessorHalfFin13_clause01488 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01513 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01514 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01515 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01516 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01517 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01518 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01519 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01520 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01521 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01524 chi hbad
              ·
                exact predecessorHalfFin13_clause01528 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01529 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01533 chi hbad
              ·
                exact predecessorHalfFin13_clause01535 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01537 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01538 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01539 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01540 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01541 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01542 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01543 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01544 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01545 chi hbad
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
              exact predecessorHalfFin13_clause01546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01547 chi hbad
              ·
                exact predecessorHalfFin13_clause01548 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01552 chi hbad
              ·
                exact predecessorHalfFin13_clause01553 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01555 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01557 chi hbad
              ·
                exact predecessorHalfFin13_clause01559 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01561 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01562 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01563 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01564 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01565 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01566 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01567 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01568 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01569 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01570 chi hbad
              ·
                exact predecessorHalfFin13_clause01571 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01576 chi hbad
              ·
                exact predecessorHalfFin13_clause01577 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01581 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01583 chi hbad
              ·
                exact predecessorHalfFin13_clause01584 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01585 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01586 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01587 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01588 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01589 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01590 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01591 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01592 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01593 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01594 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01595 chi hbad
              ·
                exact predecessorHalfFin13_clause01596 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01600 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01601 chi hbad
              ·
                exact predecessorHalfFin13_clause01603 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01607 chi hbad
              ·
                exact predecessorHalfFin13_clause01608 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01609 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01610 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01611 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01612 chi hone hbad

end ErdosSzekeres

end
