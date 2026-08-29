module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk004
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk005

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 006. -/

theorem predecessorHalfFin13_rejectSemanticSegment006
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) ∨
      (PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi))) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) ∨
      (¬PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi))) ∨
      ((¬PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) ∨
      (PredecessorHalfFin13Atom0018 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi))))) ∨
      ((((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) ∨
      ((PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0383 chi) ∨
      (PredecessorHalfFin13Atom0018 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi))) ∨
      ((¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) ∨
      ((¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) ∨
      (¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi) ∨
      ((PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) ∨
      (PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi))) ∨
      ((PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) ∨
      ((PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi) ∨
      (¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) ∨
      ((¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) ∨
      (¬PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi))) ∨
      ((¬PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) ∨
      ((PredecessorHalfFin13Atom0019 chi ∧
      ¬PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) ∨
      (PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi)))) ∨
      (((PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0385 chi) ∨
      ((PredecessorHalfFin13Atom0019 chi ∧
      PredecessorHalfFin13Atom0021 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi))))) ∨
      ((((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi)) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0387 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0031 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi)))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi))))) ∨
      ((((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0032 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi)))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0389 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0033 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi)))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi)) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi))))))))) := by
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
              exact predecessorHalfFin13_clause02308 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02309 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02310 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02311 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02312 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02313 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02315 chi hbad
              ·
                exact predecessorHalfFin13_clause02316 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02321 chi hbad
              ·
                exact predecessorHalfFin13_clause02324 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02327 chi hbad
              ·
                exact predecessorHalfFin13_clause02328 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02353 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02354 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02355 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02356 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02357 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02358 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02359 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02360 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02361 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02362 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02363 chi hbad
              ·
                exact predecessorHalfFin13_clause02364 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02369 chi hbad
              ·
                exact predecessorHalfFin13_clause02373 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02376 chi hbad
              ·
                exact predecessorHalfFin13_clause02401 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02402 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02403 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02404 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02405 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02406 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02407 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02408 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02409 chi hbad
              ·
                exact predecessorHalfFin13_clause02410 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02416 chi hbad
              ·
                exact predecessorHalfFin13_clause02417 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02419 chi hbad
              ·
                exact predecessorHalfFin13_clause02421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02423 chi hbad
              ·
                exact predecessorHalfFin13_clause02424 chi hbad
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
              exact predecessorHalfFin13_clause02425 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02426 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02427 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02428 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02429 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02430 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02431 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02432 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02433 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02434 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02436 chi hbad
              ·
                exact predecessorHalfFin13_clause02440 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02444 chi hbad
              ·
                exact predecessorHalfFin13_clause02445 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02447 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02448 chi hbad
              ·
                exact predecessorHalfFin13_clause02449 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02450 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02451 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02452 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02453 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02454 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02455 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02456 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02457 chi hbad
              ·
                exact predecessorHalfFin13_clause02458 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02460 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02464 chi hbad
              ·
                exact predecessorHalfFin13_clause02465 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02466 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02469 chi hbad
              ·
                exact predecessorHalfFin13_clause02470 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02472 chi hbad
              ·
                exact predecessorHalfFin13_clause02473 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02474 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02475 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02476 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02477 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02478 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02479 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02480 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02481 chi hbad
              ·
                exact predecessorHalfFin13_clause02482 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02484 chi hbad
              ·
                exact predecessorHalfFin13_clause02486 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02488 chi hbad
              ·
                exact predecessorHalfFin13_clause02489 chi hbad

end ErdosSzekeres

end
