module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk002
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk003

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 003. -/

theorem predecessorHalfFin13_rejectSemanticSegment003
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi)))) ∨
      (((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0361 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0361 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0361 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0361 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0362 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0362 chi)))) ∨
      (((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0362 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0362 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi)) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0363 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0365 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0365 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0365 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0365 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi)))) ∨
      (((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0365 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi))) ∨
      (((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi)) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi) ∨
      (PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi) ∨
      ((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi) ∨
      (PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi))) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      (PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi))) ∨
      ((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      (PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi))))) ∨
      ((((PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi))) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0147 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi)))) ∨
      (((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0147 chi) ∨
      ((PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi) ∨
      (PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0147 chi))) ∨
      (((PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0147 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi)) ∨
      ((¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0367 chi) ∨
      (¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0367 chi))))))))) := by
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
              exact predecessorHalfFin13_clause01775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01776 chi hbad
              ·
                exact predecessorHalfFin13_clause01777 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01778 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01779 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01780 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01781 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01782 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01783 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01784 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01785 chi hbad
              ·
                exact predecessorHalfFin13_clause01786 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01788 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01792 chi hbad
              ·
                exact predecessorHalfFin13_clause01793 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01799 chi hbad
              ·
                exact predecessorHalfFin13_clause01800 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01801 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01802 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01803 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01804 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01805 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01806 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01807 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01808 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01809 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01812 chi hbad
              ·
                exact predecessorHalfFin13_clause01816 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01821 chi hbad
              ·
                exact predecessorHalfFin13_clause01823 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01825 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01826 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01827 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01828 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01829 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01830 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01831 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01832 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01833 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01834 chi hbad
              ·
                exact predecessorHalfFin13_clause01836 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01840 chi hbad
              ·
                exact predecessorHalfFin13_clause01841 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01844 chi hbad
              ·
                exact predecessorHalfFin13_clause01845 chi hbad
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
              exact predecessorHalfFin13_clause01846 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01847 chi hbad
              ·
                exact predecessorHalfFin13_clause01848 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01873 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01874 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01875 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01876 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01877 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01878 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01879 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01880 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01881 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01884 chi hbad
              ·
                exact predecessorHalfFin13_clause01888 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01891 chi hbad
              ·
                exact predecessorHalfFin13_clause01893 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01896 chi hbad
              ·
                exact predecessorHalfFin13_clause01897 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01898 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01899 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01900 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01901 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01902 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01903 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01904 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01906 chi hbad
              ·
                exact predecessorHalfFin13_clause01908 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01911 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01912 chi hbad
              ·
                exact predecessorHalfFin13_clause01913 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01914 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01916 chi hbad
              ·
                exact predecessorHalfFin13_clause01917 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01919 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01920 chi hbad
              ·
                exact predecessorHalfFin13_clause01921 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01922 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01923 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01924 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01925 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01926 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01927 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01928 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01930 chi hbad
              ·
                exact predecessorHalfFin13_clause01931 chi hbad

end ErdosSzekeres

end
