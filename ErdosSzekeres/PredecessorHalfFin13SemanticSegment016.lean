module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk012
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk013

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 016. -/

theorem predecessorHalfFin13_rejectSemanticSegment016
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi))) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi)))) ∨
      (((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi))) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi))) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi))) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0458 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi))) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi)))) ∨
      (((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi))) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi))) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0459 chi)))) ∨
      (((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi))) ∨
      (((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi)) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi))) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) ∨
      ((¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) ∨
      (¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi))) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) ∨
      ((PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0461 chi) ∨
      (PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi))) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi)))) ∨
      (((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi))) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0462 chi))) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi))) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi))) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi)))) ∨
      (((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) ∨
      ((PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi))) ∨
      (((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) ∨
      (¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi)) ∨
      ((¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) ∨
      (PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi))))))))) := by
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
              exact predecessorHalfFin13_clause04088 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04089 chi hbad
              ·
                exact predecessorHalfFin13_clause04090 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04092 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04096 chi hbad
              ·
                exact predecessorHalfFin13_clause04097 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04101 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04103 chi hbad
              ·
                exact predecessorHalfFin13_clause04104 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04105 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04106 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04107 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04108 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04109 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04110 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04111 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04112 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04113 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04114 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04115 chi hbad
              ·
                exact predecessorHalfFin13_clause04116 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04121 chi hbad
              ·
                exact predecessorHalfFin13_clause04125 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04127 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04128 chi hbad
              ·
                exact predecessorHalfFin13_clause04129 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04130 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04131 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04132 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04133 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04134 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04135 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04136 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04137 chi hbad
              ·
                exact predecessorHalfFin13_clause04138 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04140 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04144 chi hbad
              ·
                exact predecessorHalfFin13_clause04145 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04147 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04149 chi hbad
              ·
                exact predecessorHalfFin13_clause04151 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04177 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04178 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04179 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04180 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04181 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04182 chi hone hbad
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
              exact predecessorHalfFin13_clause04183 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04184 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04185 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04188 chi hbad
              ·
                exact predecessorHalfFin13_clause04190 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04193 chi hbad
              ·
                exact predecessorHalfFin13_clause04196 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04199 chi hbad
              ·
                exact predecessorHalfFin13_clause04200 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04201 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04202 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04203 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04204 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04205 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04206 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04207 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04208 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04209 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04212 chi hbad
              ·
                exact predecessorHalfFin13_clause04216 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04221 chi hbad
              ·
                exact predecessorHalfFin13_clause04223 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04224 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04225 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04226 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04227 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04228 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04229 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04230 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04231 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04232 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04234 chi hbad
              ·
                exact predecessorHalfFin13_clause04236 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04240 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04241 chi hbad
              ·
                exact predecessorHalfFin13_clause04245 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause04247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04248 chi hbad
              ·
                exact predecessorHalfFin13_clause04273 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04274 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04275 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause04276 chi hone hbad
              ·
                exact predecessorHalfFin13_clause04277 chi hone hbad

end ErdosSzekeres

end
