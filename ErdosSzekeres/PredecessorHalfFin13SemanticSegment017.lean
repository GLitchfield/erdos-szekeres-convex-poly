module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk013

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 017. -/

theorem predecessorHalfFin13_rejectSemanticSegment017
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi))) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi))) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi))))) ∨
      ((((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi))) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi)))) ∨
      (((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi))) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi))) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi))) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi))))) ∨
      ((((PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi))) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) ∨
      ((¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      (¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi)))) ∨
      (((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) ∨
      ((PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi))) ∨
      (((PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) ∨
      (PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi)) ∨
      ((¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      (¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      ((¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      (PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi))) ∨
      ((PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      ((PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      (PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      ((¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) ∨
      (¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi))) ∨
      ((¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) ∨
      ((PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) ∨
      (PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi))))) ∨
      ((((PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) ∨
      ((PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi)))) ∨
      (((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi))) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi))) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi)))) ∨
      (((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi))) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi))))) ∨
      ((((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi))) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) ∨
      ((¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      (¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi))) ∨
      (((¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi)) ∨
      ((PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      (PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi))))))))) := by
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
              exact predecessorHalfFin13_clause04278 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04279 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04280 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04282 chi hbad
              ·
                exact predecessorHalfFin13_clause04283 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04286 chi hbad
              ·
                exact predecessorHalfFin13_clause04288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04289 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04293 chi hbad
              ·
                exact predecessorHalfFin13_clause04295 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04297 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04298 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04299 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04300 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04301 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04302 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04303 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04304 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04305 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04306 chi hbad
              ·
                exact predecessorHalfFin13_clause04308 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04312 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04313 chi hbad
              ·
                exact predecessorHalfFin13_clause04317 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04319 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04320 chi hbad
              ·
                exact predecessorHalfFin13_clause04345 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04346 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04347 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04348 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04350 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04351 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04352 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04353 chi hbad
              ·
                exact predecessorHalfFin13_clause04354 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04356 chi hbad
              ·
                exact predecessorHalfFin13_clause04360 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04364 chi hbad
              ·
                exact predecessorHalfFin13_clause04365 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04367 chi hbad
              ·
                exact predecessorHalfFin13_clause04368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04393 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04394 chi hone hbad
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
              exact predecessorHalfFin13_clause04395 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04396 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04397 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04398 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04399 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04400 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04401 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04402 chi hbad
              ·
                exact predecessorHalfFin13_clause04404 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04409 chi hbad
              ·
                exact predecessorHalfFin13_clause04413 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04416 chi hbad
              ·
                exact predecessorHalfFin13_clause04441 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04442 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04443 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04444 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04445 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04446 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04447 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04448 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04449 chi hbad
              ·
                exact predecessorHalfFin13_clause04450 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04452 chi hbad
              ·
                exact predecessorHalfFin13_clause04456 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04461 chi hbad
              ·
                exact predecessorHalfFin13_clause04462 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04463 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04464 chi hbad
              ·
                exact predecessorHalfFin13_clause04465 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04466 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04467 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04468 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04469 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04470 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04471 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04472 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04473 chi hbad
              ·
                exact predecessorHalfFin13_clause04474 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04476 chi hbad
              ·
                exact predecessorHalfFin13_clause04478 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04480 chi hbad
              ·
                exact predecessorHalfFin13_clause04481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04485 chi hbad
              ·
                exact predecessorHalfFin13_clause04487 chi hbad

end ErdosSzekeres

end
