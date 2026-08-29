module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk001
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk002

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 002. -/

theorem predecessorHalfFin13_rejectSemanticSegment002
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0354 chi))))) ∨
      ((((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi)))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0355 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi))))) ∨
      ((((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi)))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi))) ∨
      (((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0356 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi)) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi))) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) ∨
      (¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi))) ∨
      ((¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi))))) ∨
      ((((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      ((PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0358 chi) ∨
      (PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi)))) ∨
      (((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0359 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi))) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi))) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi) ∨
      ((¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi) ∨
      (¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi))) ∨
      (((¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi)) ∨
      ((PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0360 chi) ∨
      (PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi))))))))) := by
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
              exact predecessorHalfFin13_clause01613 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01614 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01615 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01616 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01617 chi hbad
              ·
                exact predecessorHalfFin13_clause01618 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01619 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01620 chi hbad
              ·
                exact predecessorHalfFin13_clause01624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01629 chi hbad
              ·
                exact predecessorHalfFin13_clause01631 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01632 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01633 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01634 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01635 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01636 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01637 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01638 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01639 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01640 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01642 chi hbad
              ·
                exact predecessorHalfFin13_clause01644 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01649 chi hbad
              ·
                exact predecessorHalfFin13_clause01651 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01655 chi hbad
              ·
                exact predecessorHalfFin13_clause01656 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01657 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01658 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01659 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01660 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01661 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01662 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01663 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01664 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01665 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01666 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01668 chi hbad
              ·
                exact predecessorHalfFin13_clause01672 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01676 chi hbad
              ·
                exact predecessorHalfFin13_clause01677 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01679 chi hbad
              ·
                exact predecessorHalfFin13_clause01680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01705 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01706 chi hone hbad
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
              exact predecessorHalfFin13_clause01707 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01708 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01709 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01710 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01711 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01712 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01714 chi hbad
              ·
                exact predecessorHalfFin13_clause01716 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01721 chi hbad
              ·
                exact predecessorHalfFin13_clause01723 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01725 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01727 chi hbad
              ·
                exact predecessorHalfFin13_clause01728 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01729 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01730 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01731 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01732 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01733 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01734 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01735 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01736 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01737 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01739 chi hbad
              ·
                exact predecessorHalfFin13_clause01740 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01745 chi hbad
              ·
                exact predecessorHalfFin13_clause01746 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01749 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01751 chi hbad
              ·
                exact predecessorHalfFin13_clause01752 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01753 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01754 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01755 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01756 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01757 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01758 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01759 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01760 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01761 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01763 chi hbad
              ·
                exact predecessorHalfFin13_clause01764 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01768 chi hbad
              ·
                exact predecessorHalfFin13_clause01769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01772 chi hbad
              ·
                exact predecessorHalfFin13_clause01773 chi hbad

end ErdosSzekeres

end
