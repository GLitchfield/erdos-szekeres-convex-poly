module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk003
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk004

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 005. -/

theorem predecessorHalfFin13_rejectSemanticSegment005
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0154 chi) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      (¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0374 chi))) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0374 chi) ∨
      (¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0374 chi)))) ∨
      (((PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0374 chi) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      (PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0374 chi))) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi) ∨
      (¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi) ∨
      (PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi))) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi) ∨
      (PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) ∨
      (¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi))) ∨
      ((¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) ∨
      (PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      ((PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0376 chi) ∨
      (PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi))) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi))) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi))) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0377 chi)))) ∨
      (((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi))) ∨
      (((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi)) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi))) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi))) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi))) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi)))) ∨
      (((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi))) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) ∨
      ((¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi))) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0380 chi) ∨
      ((PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi))) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi) ∨
      (PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi))))) ∨
      ((((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi))) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi)))) ∨
      (((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0381 chi))) ∨
      (((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi)) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi))))))))) := by
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
              exact predecessorHalfFin13_clause02096 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02097 chi hbad
              ·
                exact predecessorHalfFin13_clause02098 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02103 chi hbad
              ·
                exact predecessorHalfFin13_clause02104 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02105 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02109 chi hbad
              ·
                exact predecessorHalfFin13_clause02111 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02137 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02138 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02139 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02140 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02141 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02142 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02143 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02144 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02145 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02146 chi hbad
              ·
                exact predecessorHalfFin13_clause02148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02153 chi hbad
              ·
                exact predecessorHalfFin13_clause02156 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02157 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02159 chi hbad
              ·
                exact predecessorHalfFin13_clause02160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02161 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02162 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02163 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02164 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02165 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02166 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02167 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02168 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02169 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02172 chi hbad
              ·
                exact predecessorHalfFin13_clause02176 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02181 chi hbad
              ·
                exact predecessorHalfFin13_clause02183 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02185 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02186 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02187 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02188 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02189 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02190 chi hone hbad
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
              exact predecessorHalfFin13_clause02191 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02192 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02193 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02196 chi hbad
              ·
                exact predecessorHalfFin13_clause02199 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02200 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02201 chi hbad
              ·
                exact predecessorHalfFin13_clause02204 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02207 chi hbad
              ·
                exact predecessorHalfFin13_clause02208 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02233 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02234 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02235 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02236 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02237 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02238 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02239 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02240 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02241 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02242 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02244 chi hbad
              ·
                exact predecessorHalfFin13_clause02248 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02252 chi hbad
              ·
                exact predecessorHalfFin13_clause02253 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02255 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02256 chi hbad
              ·
                exact predecessorHalfFin13_clause02257 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02258 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02259 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02260 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02261 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02262 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02263 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02264 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02265 chi hbad
              ·
                exact predecessorHalfFin13_clause02266 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02267 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02268 chi hbad
              ·
                exact predecessorHalfFin13_clause02272 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02273 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02277 chi hbad
              ·
                exact predecessorHalfFin13_clause02279 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02280 chi hbad
              ·
                exact predecessorHalfFin13_clause02305 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02306 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02307 chi hone hbad

end ErdosSzekeres

end
