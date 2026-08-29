module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk008
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk009

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 011. -/

theorem predecessorHalfFin13_rejectSemanticSegment011
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi) ∨
      ((PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi) ∨
      (PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi))) ∨
      ((¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      ((¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0419 chi) ∨
      (¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0419 chi) ∨
      ((¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0419 chi))) ∨
      ((PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      ((PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) ∨
      ((¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) ∨
      (¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi))) ∨
      ((¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) ∨
      ((PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi) ∨
      (PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi)))) ∨
      (((PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi) ∨
      ((PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi) ∨
      (¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi))) ∨
      ((¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0421 chi) ∨
      ((¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0421 chi) ∨
      (¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0421 chi) ∨
      ((PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0421 chi) ∨
      (PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi))) ∨
      ((PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0421 chi) ∨
      ((PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi))) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi))))) ∨
      ((((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi))) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi))) ∨
      (((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0423 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi)) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi))) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi))) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi))))) ∨
      ((((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi))) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi)) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi))) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi)))) ∨
      (((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi))) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0425 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi))) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi)))) ∨
      (((PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) ∨
      ((PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi))) ∨
      (((¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) ∨
      (¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi)) ∨
      ((¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi) ∨
      (PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0426 chi))))))))) := by
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
              exact predecessorHalfFin13_clause03174 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03175 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03176 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03178 chi hbad
              ·
                exact predecessorHalfFin13_clause03180 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03181 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03184 chi hbad
              ·
                exact predecessorHalfFin13_clause03185 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03191 chi hbad
              ·
                exact predecessorHalfFin13_clause03192 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03217 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03218 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03219 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03220 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03221 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03222 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03223 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03224 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03227 chi hbad
              ·
                exact predecessorHalfFin13_clause03228 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03233 chi hbad
              ·
                exact predecessorHalfFin13_clause03237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03240 chi hbad
              ·
                exact predecessorHalfFin13_clause03265 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03266 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03267 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03268 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03269 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03270 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03271 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03272 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03273 chi hbad
              ·
                exact predecessorHalfFin13_clause03274 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03275 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03276 chi hbad
              ·
                exact predecessorHalfFin13_clause03279 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03281 chi hbad
              ·
                exact predecessorHalfFin13_clause03285 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03287 chi hbad
              ·
                exact predecessorHalfFin13_clause03288 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03289 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03290 chi hone hbad
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
              exact predecessorHalfFin13_clause03291 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03292 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03293 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03294 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03295 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03296 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03297 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03298 chi hbad
              ·
                exact predecessorHalfFin13_clause03299 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03300 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03303 chi hbad
              ·
                exact predecessorHalfFin13_clause03304 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03305 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03308 chi hbad
              ·
                exact predecessorHalfFin13_clause03309 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03311 chi hbad
              ·
                exact predecessorHalfFin13_clause03312 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03313 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03314 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03315 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03316 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03317 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03318 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03319 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03320 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03321 chi hbad
              ·
                exact predecessorHalfFin13_clause03322 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03323 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03324 chi hbad
              ·
                exact predecessorHalfFin13_clause03328 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03330 chi hbad
              ·
                exact predecessorHalfFin13_clause03333 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03334 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03335 chi hbad
              ·
                exact predecessorHalfFin13_clause03336 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03337 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03338 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03339 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03340 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03341 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03342 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause03343 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03344 chi hone hbad
              ·
                exact predecessorHalfFin13_clause03345 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03346 chi hbad
              ·
                exact predecessorHalfFin13_clause03348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause03352 chi hbad
              ·
                exact predecessorHalfFin13_clause03353 chi hbad

end ErdosSzekeres

end
