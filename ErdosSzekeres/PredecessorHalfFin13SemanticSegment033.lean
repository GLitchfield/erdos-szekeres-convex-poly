module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk025
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk026

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 033. -/

theorem predecessorHalfFin13_rejectSemanticSegment033
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0739 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi))) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0739 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi))) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi))))) ∨
      ((((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi))) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0740 chi) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0740 chi)))) ∨
      (((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0740 chi))) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0144 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi))) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi)))) ∨
      (((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi))) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi) ∨
      ((¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      (¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi))))) ∨
      ((((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi))) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      ((PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0741 chi) ∨
      (PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi))) ∨
      (((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi)) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi))) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi)))) ∨
      (((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi))) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0742 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi))) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi)))) ∨
      (((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi))) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi))) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0743 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0142 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi))) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi))))) ∨
      ((((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi))) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi) ∨
      ((¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi))) ∨
      (((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi)) ∨
      ((PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0143 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0143 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi))))))))) := by
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
              exact predecessorHalfFin13_clause10865 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10866 chi hbad
              ·
                exact predecessorHalfFin13_clause10869 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10871 chi hbad
              ·
                exact predecessorHalfFin13_clause10872 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10873 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10874 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10875 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10876 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10877 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10878 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10879 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10880 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10881 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10884 chi hbad
              ·
                exact predecessorHalfFin13_clause10888 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10893 chi hbad
              ·
                exact predecessorHalfFin13_clause10894 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10896 chi hbad
              ·
                exact predecessorHalfFin13_clause10897 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10898 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10899 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10900 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10901 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10902 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10903 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10904 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10905 chi hbad
              ·
                exact predecessorHalfFin13_clause10906 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10908 chi hbad
              ·
                exact predecessorHalfFin13_clause10912 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10915 chi hbad
              ·
                exact predecessorHalfFin13_clause10916 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10919 chi hbad
              ·
                exact predecessorHalfFin13_clause10920 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10921 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10922 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10923 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10924 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10925 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10926 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10927 chi hone hbad
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
              exact predecessorHalfFin13_clause10928 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10929 chi hbad
              ·
                exact predecessorHalfFin13_clause10930 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10932 chi hbad
              ·
                exact predecessorHalfFin13_clause10936 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10937 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10941 chi hbad
              ·
                exact predecessorHalfFin13_clause10942 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10943 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10944 chi hbad
              ·
                exact predecessorHalfFin13_clause10945 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10946 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10947 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10948 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10949 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10950 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10951 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10952 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10953 chi hbad
              ·
                exact predecessorHalfFin13_clause10954 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10955 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10956 chi hbad
              ·
                exact predecessorHalfFin13_clause10959 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10961 chi hbad
              ·
                exact predecessorHalfFin13_clause10964 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10965 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10967 chi hbad
              ·
                exact predecessorHalfFin13_clause10968 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10969 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10970 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10971 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10972 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10973 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10974 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10975 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10976 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10977 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10980 chi hbad
              ·
                exact predecessorHalfFin13_clause10981 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10984 chi hbad
              ·
                exact predecessorHalfFin13_clause10985 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10986 chi hbad
              ·
                exact predecessorHalfFin13_clause10987 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10988 chi hbad
              ·
                exact predecessorHalfFin13_clause10989 chi hbad

end ErdosSzekeres

end
