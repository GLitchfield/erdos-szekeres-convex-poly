module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk000

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 000. -/

theorem predecessorHalfFin13_rejectSemanticSegment000
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      ¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0342 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0013 chi ∧
      PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0343 chi))))) ∨
      ((((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0014 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi)) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0344 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0015 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi))))) ∨
      ((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0345 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0016 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi)))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi))) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi))))) ∨
      ((((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0346 chi))) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0017 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) ∨
      ((¬PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi))) ∨
      (((PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi) ∨
      (PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi)) ∨
      ((PredecessorHalfFin13Atom0012 chi ∧
      PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0127 chi) ∨
      (¬PredecessorHalfFin13Atom0012 chi ∧
      ¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi))))))))) := by
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
              exact predecessorHalfFin13_clause01321 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01322 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01323 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01324 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01325 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01326 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01327 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01328 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01329 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01330 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01331 chi hbad
              ·
                exact predecessorHalfFin13_clause01332 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01336 chi hbad
              ·
                exact predecessorHalfFin13_clause01337 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01340 chi hbad
              ·
                exact predecessorHalfFin13_clause01341 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01343 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01344 chi hbad
              ·
                exact predecessorHalfFin13_clause01345 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01346 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01347 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01348 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01350 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01351 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01352 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01353 chi hbad
              ·
                exact predecessorHalfFin13_clause01354 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01356 chi hbad
              ·
                exact predecessorHalfFin13_clause01360 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01365 chi hbad
              ·
                exact predecessorHalfFin13_clause01367 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01369 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01370 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01371 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01372 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01373 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01374 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01375 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01376 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01377 chi hbad
              ·
                exact predecessorHalfFin13_clause01378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01380 chi hbad
              ·
                exact predecessorHalfFin13_clause01384 chi hbad
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
              exact predecessorHalfFin13_clause01385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01387 chi hbad
              ·
                exact predecessorHalfFin13_clause01388 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01389 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01391 chi hbad
              ·
                exact predecessorHalfFin13_clause01392 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01393 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01394 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01395 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01396 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01397 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01398 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01399 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01400 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01401 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01403 chi hbad
              ·
                exact predecessorHalfFin13_clause01404 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01409 chi hbad
              ·
                exact predecessorHalfFin13_clause01413 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01416 chi hbad
              ·
                exact predecessorHalfFin13_clause01417 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01418 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01419 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01420 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01421 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01422 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01423 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01424 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01425 chi hbad
              ·
                exact predecessorHalfFin13_clause01426 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01427 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01428 chi hbad
              ·
                exact predecessorHalfFin13_clause01432 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01433 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01437 chi hbad
              ·
                exact predecessorHalfFin13_clause01439 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01440 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01441 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01442 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause01443 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01444 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01445 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01446 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01447 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause01448 chi hone hbad
              ·
                exact predecessorHalfFin13_clause01449 chi hbad

end ErdosSzekeres

end
