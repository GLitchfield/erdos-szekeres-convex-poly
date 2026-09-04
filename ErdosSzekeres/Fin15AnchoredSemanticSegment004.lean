module

public import ErdosSzekeres.Fin15AnchoredClauseChunk007
public import ErdosSzekeres.Fin15AnchoredClauseChunk008
public import ErdosSzekeres.Fin15AnchoredClauseChunk009

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 004. -/

theorem fin15Anchored_rejectSemanticSegment004
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi)))) ∨
      ((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi))))) ∨
      (((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi)))) ∨
      ((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi)))) ∨
      ((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi))))) ∨
      (((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi)))) ∨
      ((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi)))) ∨
      ((((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi))))) ∨
      (((((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi)))) ∨
      ((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi)))))) ∨
      ((((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi)))) ∨
      ((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi))))) ∨
      (((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi)))) ∨
      ((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi)))) ∨
      ((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi))))) ∨
      (((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi)))) ∨
      ((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi)))))) ∨
      ((((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi)))) ∨
      ((((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi))))) ∨
      (((((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi)))) ∨
      ((((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi)) ∨
      ((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) ∨
      ((Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi))) ∨
      (((Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi)) ∨
      ((¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi)))) ∨
      ((((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi)) ∨
      ((Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) ∨
      (Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi))) ∨
      (((Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0332 chi)) ∨
      ((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0332 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0332 chi))))) ∨
      (((((¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi)) ∨
      ((¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi))) ∨
      (((Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi)) ∨
      ((Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi)))) ∨
      ((((¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi)) ∨
      ((¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi))) ∨
      (((Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi)) ∨
      ((Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi)) ∨
      ((¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi))) ∨
      (((Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi)) ∨
      ((Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi)))) ∨
      ((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi))))) ∨
      (((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi)))) ∨
      ((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi)))))))))) := by
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause01009 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01010 chi hone hbad
                ·
                  exact fin15Anchored_clause01011 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01012 chi hone hbad
                ·
                  exact fin15Anchored_clause01013 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01014 chi hone hbad
                ·
                  exact fin15Anchored_clause01015 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01016 chi hone hbad
                ·
                  exact fin15Anchored_clause01017 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01018 chi hone hbad
                ·
                  exact fin15Anchored_clause01019 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01020 chi hone hbad
                ·
                  exact fin15Anchored_clause01021 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01022 chi hone hbad
                ·
                  exact fin15Anchored_clause01023 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01024 chi hone hbad
                ·
                  exact fin15Anchored_clause01025 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01026 chi hone hbad
                ·
                  exact fin15Anchored_clause01027 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01028 chi hone hbad
                ·
                  exact fin15Anchored_clause01029 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01030 chi hone hbad
                ·
                  exact fin15Anchored_clause01031 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01032 chi hone hbad
                ·
                  exact fin15Anchored_clause01033 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01034 chi hone hbad
                ·
                  exact fin15Anchored_clause01035 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01036 chi hone hbad
                ·
                  exact fin15Anchored_clause01037 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01038 chi hone hbad
                ·
                  exact fin15Anchored_clause01039 chi hone hbad
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
                  exact fin15Anchored_clause01040 chi hone hbad
                ·
                  exact fin15Anchored_clause01041 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01042 chi hone hbad
                ·
                  exact fin15Anchored_clause01043 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01044 chi hone hbad
                ·
                  exact fin15Anchored_clause01045 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01046 chi hone hbad
                ·
                  exact fin15Anchored_clause01047 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01048 chi hone hbad
                ·
                  exact fin15Anchored_clause01049 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01050 chi hone hbad
                ·
                  exact fin15Anchored_clause01051 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01052 chi hone hbad
                ·
                  exact fin15Anchored_clause01053 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01054 chi hone hbad
                ·
                  exact fin15Anchored_clause01055 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01056 chi hone hbad
                ·
                  exact fin15Anchored_clause01057 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01058 chi hone hbad
                ·
                  exact fin15Anchored_clause01059 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01060 chi hone hbad
                ·
                  exact fin15Anchored_clause01061 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01062 chi hone hbad
                ·
                  exact fin15Anchored_clause01063 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01064 chi hone hbad
                ·
                  exact fin15Anchored_clause01065 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01066 chi hone hbad
                ·
                  exact fin15Anchored_clause01067 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01068 chi hone hbad
                ·
                  exact fin15Anchored_clause01069 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01070 chi hone hbad
                ·
                  exact fin15Anchored_clause01071 chi hone hbad
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
                exact fin15Anchored_clause01072 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01073 chi hone hbad
                ·
                  exact fin15Anchored_clause01074 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01075 chi hone hbad
                ·
                  exact fin15Anchored_clause01076 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01077 chi hone hbad
                ·
                  exact fin15Anchored_clause01078 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01079 chi hone hbad
                ·
                  exact fin15Anchored_clause01080 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01081 chi hone hbad
                ·
                  exact fin15Anchored_clause01082 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01083 chi hone hbad
                ·
                  exact fin15Anchored_clause01084 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01085 chi hone hbad
                ·
                  exact fin15Anchored_clause01086 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01087 chi hone hbad
                ·
                  exact fin15Anchored_clause01088 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01089 chi hone hbad
                ·
                  exact fin15Anchored_clause01090 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01091 chi hone hbad
                ·
                  exact fin15Anchored_clause01092 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01093 chi hone hbad
                ·
                  exact fin15Anchored_clause01094 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01095 chi hone hbad
                ·
                  exact fin15Anchored_clause01096 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01097 chi hone hbad
                ·
                  exact fin15Anchored_clause01098 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01099 chi hone hbad
                ·
                  exact fin15Anchored_clause01100 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01101 chi hone hbad
                ·
                  exact fin15Anchored_clause01102 chi hone hbad
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
                  exact fin15Anchored_clause01103 chi hone hbad
                ·
                  exact fin15Anchored_clause01104 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01105 chi hone hbad
                ·
                  exact fin15Anchored_clause01106 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01107 chi hone hbad
                ·
                  exact fin15Anchored_clause01108 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01109 chi hone hbad
                ·
                  exact fin15Anchored_clause01110 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01111 chi hone hbad
                ·
                  exact fin15Anchored_clause01112 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01113 chi hone hbad
                ·
                  exact fin15Anchored_clause01114 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01115 chi hone hbad
                ·
                  exact fin15Anchored_clause01116 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01117 chi hone hbad
                ·
                  exact fin15Anchored_clause01118 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01119 chi hone hbad
                ·
                  exact fin15Anchored_clause01120 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01121 chi hone hbad
                ·
                  exact fin15Anchored_clause01122 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01123 chi hone hbad
                ·
                  exact fin15Anchored_clause01124 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01125 chi hone hbad
                ·
                  exact fin15Anchored_clause01126 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01127 chi hone hbad
                ·
                  exact fin15Anchored_clause01128 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01129 chi hone hbad
                ·
                  exact fin15Anchored_clause01130 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01131 chi hone hbad
                ·
                  exact fin15Anchored_clause01132 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01133 chi hone hbad
                ·
                  exact fin15Anchored_clause01134 chi hone hbad
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause01135 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01136 chi hone hbad
                ·
                  exact fin15Anchored_clause01137 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01138 chi hone hbad
                ·
                  exact fin15Anchored_clause01139 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01140 chi hone hbad
                ·
                  exact fin15Anchored_clause01141 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01142 chi hone hbad
                ·
                  exact fin15Anchored_clause01143 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01144 chi hone hbad
                ·
                  exact fin15Anchored_clause01145 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01146 chi hone hbad
                ·
                  exact fin15Anchored_clause01147 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01148 chi hone hbad
                ·
                  exact fin15Anchored_clause01149 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01150 chi hone hbad
                ·
                  exact fin15Anchored_clause01151 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01152 chi hone hbad
                ·
                  exact fin15Anchored_clause01153 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01154 chi hone hbad
                ·
                  exact fin15Anchored_clause01155 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01156 chi hone hbad
                ·
                  exact fin15Anchored_clause01157 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01158 chi hone hbad
                ·
                  exact fin15Anchored_clause01159 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01160 chi hone hbad
                ·
                  exact fin15Anchored_clause01161 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01162 chi hone hbad
                ·
                  exact fin15Anchored_clause01163 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01164 chi hone hbad
                ·
                  exact fin15Anchored_clause01165 chi hone hbad
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
                  exact fin15Anchored_clause01166 chi hone hbad
                ·
                  exact fin15Anchored_clause01167 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01168 chi hone hbad
                ·
                  exact fin15Anchored_clause01169 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01170 chi hone hbad
                ·
                  exact fin15Anchored_clause01171 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01172 chi hone hbad
                ·
                  exact fin15Anchored_clause01173 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01174 chi hone hbad
                ·
                  exact fin15Anchored_clause01175 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01176 chi hone hbad
                ·
                  exact fin15Anchored_clause01177 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01178 chi hone hbad
                ·
                  exact fin15Anchored_clause01179 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01180 chi hone hbad
                ·
                  exact fin15Anchored_clause01181 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01182 chi hone hbad
                ·
                  exact fin15Anchored_clause01183 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01184 chi hone hbad
                ·
                  exact fin15Anchored_clause01185 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01186 chi hone hbad
                ·
                  exact fin15Anchored_clause01187 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01188 chi hone hbad
                ·
                  exact fin15Anchored_clause01189 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01190 chi hone hbad
                ·
                  exact fin15Anchored_clause01191 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01192 chi hone hbad
                ·
                  exact fin15Anchored_clause01193 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01194 chi hone hbad
                ·
                  exact fin15Anchored_clause01195 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01196 chi hone hbad
                ·
                  exact fin15Anchored_clause01197 chi hone hbad
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
                exact fin15Anchored_clause01198 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01199 chi hone hbad
                ·
                  exact fin15Anchored_clause01200 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01201 chi hone hbad
                ·
                  exact fin15Anchored_clause01202 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01203 chi hone hbad
                ·
                  exact fin15Anchored_clause01204 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01205 chi hone hbad
                ·
                  exact fin15Anchored_clause01206 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01207 chi hone hbad
                ·
                  exact fin15Anchored_clause01208 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01209 chi hone hbad
                ·
                  exact fin15Anchored_clause01210 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01211 chi hone hbad
                ·
                  exact fin15Anchored_clause01212 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01213 chi hone hbad
                ·
                  exact fin15Anchored_clause01214 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01215 chi hone hbad
                ·
                  exact fin15Anchored_clause01216 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01217 chi hone hbad
                ·
                  exact fin15Anchored_clause01218 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01219 chi hone hbad
                ·
                  exact fin15Anchored_clause01220 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01221 chi hone hbad
                ·
                  exact fin15Anchored_clause01222 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01223 chi hone hbad
                ·
                  exact fin15Anchored_clause01224 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01225 chi hone hbad
                ·
                  exact fin15Anchored_clause01226 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01227 chi hone hbad
                ·
                  exact fin15Anchored_clause01228 chi hone hbad
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
                  exact fin15Anchored_clause01229 chi hone hbad
                ·
                  exact fin15Anchored_clause01230 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01231 chi hone hbad
                ·
                  exact fin15Anchored_clause01232 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01233 chi hone hbad
                ·
                  exact fin15Anchored_clause01234 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01235 chi hone hbad
                ·
                  exact fin15Anchored_clause01236 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01237 chi hone hbad
                ·
                  exact fin15Anchored_clause01238 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01239 chi hone hbad
                ·
                  exact fin15Anchored_clause01240 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01241 chi hone hbad
                ·
                  exact fin15Anchored_clause01242 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01243 chi hone hbad
                ·
                  exact fin15Anchored_clause01244 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01245 chi hone hbad
                ·
                  exact fin15Anchored_clause01246 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01247 chi hone hbad
                ·
                  exact fin15Anchored_clause01248 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01249 chi hone hbad
                ·
                  exact fin15Anchored_clause01250 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01251 chi hone hbad
                ·
                  exact fin15Anchored_clause01252 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01253 chi hone hbad
                ·
                  exact fin15Anchored_clause01254 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01255 chi hone hbad
                ·
                  exact fin15Anchored_clause01256 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01257 chi hone hbad
                ·
                  exact fin15Anchored_clause01258 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01259 chi hone hbad
                ·
                  exact fin15Anchored_clause01260 chi hone hbad

end ErdosSzekeres

end
